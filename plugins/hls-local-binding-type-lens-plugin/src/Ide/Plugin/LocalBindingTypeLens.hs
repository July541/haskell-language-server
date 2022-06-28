{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Ide.Plugin.LocalBindingTypeLens where
import           Control.Lens               ((^.))
import           Control.Monad              (forM, void, guard)
import           Control.Monad.IO.Class     (liftIO)
import           Data.Aeson                 (Value (Null), toJSON)
import           Data.Generics
import           Data.Maybe                 (fromMaybe, mapMaybe, maybeToList)
import qualified Data.Text                  as T
import           Development.IDE            hiding (pluginHandlers)
import           Development.IDE.GHC.Compat
import           Ide.PluginUtils
import           Ide.Types                  hiding (pluginId)
import           Language.LSP.Server        (sendRequest)
import           Language.LSP.Types
import qualified Language.LSP.Types.Lens    as L
import Control.Monad.Extra (concatForM)

descriptor :: PluginDescriptor IdeState
descriptor = (defaultPluginDescriptor pluginId)
    { pluginHandlers = mkPluginHandler STextDocumentCodeLens codeLens
    , pluginCommands = [PluginCommand typeLensCommandId "Add type sig for where clasure" codeLensCommandHandler]
    }

pluginId :: PluginId
pluginId = "localBindingTypeLens"

typeLensCommandId :: CommandId
typeLensCommandId = "localBindingTypeLens.addLocalBinding"

-- | All where clasure
findWhereQ :: GenericQ [LHsLocalBinds GhcTc]
findWhereQ = everything (<>) $ mkQ [] (pure . findWhere)
    where
        findWhere :: GRHSs GhcTc (LHsExpr GhcTc) -> LHsLocalBinds GhcTc
        findWhere = grhssLocalBinds

-- findLocalValBindsQ :: GenericQ [HsValBindsLR GhcTc GhcTc]
-- findLocalValBindsQ = everything (<>) $ mkQ [] (maybeToList . findLocalValBinds)
--     where
--         findLocalValBinds (HsValBinds _ bind) = Just bind
--         findLocalValBinds _ = Nothing

-- | One binding expression with its name(s) and location.
data WhereBinding = WhereBinding
    { bindingId :: [Id]
    -- ^ There may multiple ids for one expression.
    -- e.g. @(a,b) = (1,True)@
    , bindingLoc :: SrcSpan
    -- ^ Location for the whole binding.
    -- Here we use the this to render the type signature at the proper place.
    --
    -- Example: For @(a,b) = (1,True)@, it will print the signature after the
    -- open parenthesis instead of the above of the whole expression.
    }

-- | Existed bindings in a where clause.
data WhereBindings = WhereBindings
    { bindings :: [WhereBinding]
    , existedSigNames :: [Name]
    -- ^ Names of existing signatures.
    -- It is used to hide type lens for existing signatures.
    }

-- | Find all bindings for **one** where clasure.
findBindingsQ :: GenericQ (Maybe WhereBindings)
findBindingsQ = something (mkQ Nothing findBindings)
    where
        findBindings :: NHsValBindsLR GhcTc -> Maybe WhereBindings
        findBindings (NValBinds binds sigs) =
            Just $ WhereBindings
                { bindings = mapMaybe (something (mkQ Nothing findBindingIds) . snd) binds
                , existedSigNames = concatMap findSigIds sigs
                }

        findBindingIds :: LHsBindLR GhcTc GhcTc -> Maybe WhereBinding
        findBindingIds (L l FunBind{..}) = Just $ WhereBinding (pure $ unLoc fun_id) l
        findBindingIds (L l PatBind{..}) =
            let ids = (everything (<>) $ mkQ [] (maybeToList . findIdFromPat)) pat_lhs
            in Just $ WhereBinding ids l
        findBindingIds _ = Nothing

        -- | Example: Find `a` and `b` from @(a,b) = (1,True)@
        findIdFromPat :: Pat GhcTc -> Maybe Id
        findIdFromPat (VarPat _ (L _ id)) = Just id
        findIdFromPat _ = Nothing

        findSigIds (L _ (TypeSig _ names _)) = map unLoc names
        findSigIds _                         = []

findIdQ :: GenericQ (Maybe ([Id], [Name]))
findIdQ = something (mkQ Nothing findIds)
    where
        findIds :: NHsValBindsLR GhcTc -> Maybe ([Id], [Name])
        findIds (NValBinds binds sigs) =
            Just ( concat $ mapMaybe (something (mkQ Nothing findId) . snd) binds
                 , concatMap findSigIds sigs
                 )
        -- TODO: Add PatBind

        findId :: HsBindLR GhcTc GhcTc -> Maybe [Id]
        findId FunBind{..} = Just $ pure $ unLoc fun_id
        findId PatBind{..} = Just $ (everything (<>) $ mkQ [] (maybeToList . findIdFromPat)) pat_lhs
        findId _           = Nothing

        findIdFromPat :: Pat GhcTc -> Maybe Id
        findIdFromPat (VarPat _ name) = Just $ unLoc name
        findIdFromPat _               = Nothing

        -- findSigIds :: Sig GhcTc -> [Name]
        findSigIds (L _ (TypeSig _ names _)) = map unLoc names
        findSigIds _                         = []

-- findId :: LHsLocalBinds GhcTc -> Maybe Id
-- findId (L _ localBind) = case localBind of
--     HsValBinds _ valBind -> case valBind of
--         XValBindsLR bind -> Nothing
--         _ -> Nothing
--     _ -> Nothing

codeLens :: PluginMethodHandler IdeState TextDocumentCodeLens
codeLens state plId CodeLensParams{..} = pluginResponse $ do
    nfp <- getNormalizedFilePath plId uri
    tmr <- handleMaybeM "Unable to typechecking"
        $ liftIO
        $ runAction "localBindingTypeLens.TypeCheck" state
        $ use TypeCheck nfp
    (hscEnv -> hsc) <- handleMaybeM "ghcse"
        $ liftIO
        $ runAction "localBindingTypeLens.GhcSession" state
        $ use GhcSession nfp
    let tcGblEnv = tmrTypechecked tmr
        rdrEnv = tcg_rdr_env tcGblEnv

        getSignature :: Id -> IO T.Text
        getSignature id = do
            let name = idName id
            (_, fromMaybe [] -> sig) <- liftIO
                $ initTcWithGbl hsc tcGblEnv (realSrcLocSpan $ mkRealSrcLoc "<dummy>" 1 1)
                $ getType id
            pure (printOutputable name <> " :: " <> T.pack sig)

        showType ty = showSDocForUser' hsc (mkPrintUnqualifiedDefault hsc rdrEnv) (pprSigmaType ty)

        getType id = do
            env <- tcInitTidyEnv
            let (_, ty) = tidyOpenType env (idType id) -- Try tidyTypes and tidyOpenTypes
            return $ showType $ ty

        binds = tcg_binds tcGblEnv -- TypeCheckedSource
        wheres = findWhereQ binds -- All where clauses

        localBindings = mapMaybe findBindingsQ wheres

        ids = concatMap fst $ mapMaybe findIdQ wheres
        existedSigs = map getSrcSpan $ concatMap snd $ mapMaybe findIdQ wheres
        idsWithoutSig = filter (\x -> getSrcSpan (idName x) `notElem` existedSigs) ids

        bindingLenses :: [Id] -> SrcSpan -> IO [CodeLens]
        bindingLenses ids span = case srcSpanToRange span of
            Nothing -> pure []
            Just range -> forM ids $ \id -> do
                sig <- getSignature id
                pure $ generateLens plId range sig

    -- liftIO $ print $ printOutputable existedSigs
    -- liftIO $ print $ printOutputable $ map getSrcSpan idsWithoutSig

    -- liftIO $ print 112

    lenses <- concatForM localBindings $ \WhereBindings{..} -> do
        let sigSpans = getSrcSpan <$> existedSigNames
        liftIO $ concatForM bindings $ \WhereBinding{..} -> do
            let idsWithoutSig = filter (\x -> getSrcSpan (idName x) `notElem` sigSpans) bindingId
            bindingLenses idsWithoutSig bindingLoc

    -- res <- forM idsWithoutSig $ \id -> do
    --     (_, fromMaybe [] -> sig) <- liftIO
    --         $ initTcWithGbl hsc tcGblEnv (realSrcLocSpan $ mkRealSrcLoc "<dummy>" 1 1)
    --         $ getType id
    --     -- liftIO $ putStrLn sig
    --     pure (idName id, sig)
    -- let lens = fromMaybe [] $  for res $ \(name, sig) ->
    --             case srcSpanToRange (getSrcSpan name) of
    --                 Just range -> Just $ generateLens plId range (printOutputable name <> " :: " <> T.pack sig)
    --                 Nothing    -> Nothing
    -- liftIO $ mapM_ (print . printOutputable) $ map (getSrcSpan . idName) ids
    pure $ List lenses
    where
        -- uri :: Uri
        uri = _textDocument ^. L.uri

        generateLens :: PluginId -> Range -> T.Text -> CodeLens
        generateLens plId range title =
            let cmd = mkLspCommand plId typeLensCommandId title (Just [toJSON (makeEdit range title)])
            in  CodeLens range (Just cmd) Nothing
            where
                -- makeEdit :: Range -> T.Text -> WorkspaceEdit
            makeEdit range text =
                let startPos = range ^. L.start
                    -- insertLine =startPos ^. L.line
                    insertChar = startPos ^. L.character
                    insertRange = Range startPos startPos
                in WorkspaceEdit
                        (pure [(uri, List
                        [TextEdit insertRange
                            (text <> "\n" <> T.replicate (fromIntegral insertChar) " ")])]
                        )
                        Nothing
                        Nothing

codeLensCommandHandler :: CommandFunction IdeState WorkspaceEdit
codeLensCommandHandler _ wedit = do
    void $ sendRequest SWorkspaceApplyEdit (ApplyWorkspaceEditParams Nothing wedit) (const $ pure ())
    return $ Right Null
