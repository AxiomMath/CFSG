module

public import Certificates.Data.Kernel.LocalQT.CoreS
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
import CFSG.Certificates.Kernel.LocalQTCoreCSnd.HypA
public import Certificates.Data.Kernel.LocalQT.ChainInj

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.KC.LQT.W CFSG.KC.LQT.L

theorem coreC_sound {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (kOrd : ℕ) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hI : CFSG.KC.LQT.L.chainInj n C = true)
    (hg : CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G)) (inC n C (chainF C)) = true)
    (hw : wordsC n C (c.nW.map (evalWK n G)) W c.depth = true)
    (hcl : ∀ j < n, chainChunk n C (fun s => CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G))
      fun g => inC n C (chainF C) (CFSG.KC.LQT.P.mul n s g)) j = true)
    (hL : chainF C = c.nOrd)
    (hN : normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (hO : orbK n G (c.eW.map (evalWK n G)) c.rT c.nOrd kOrd = true) :
    c.coreCheckT (gs.map RN.enc) kOrd = true :=
  CFSG.KC.LQT.Syl.CoreSnd.coreC_snd gs hG c kOrd C W hE hC hI hg hw hcl hL hN hO

theorem hypAC_sound {n : ℕ} (gs : List (Perm (Fin n))) {G : List ℕ} (hG : gs.map codeP = G)
    (c : ECert) (C : List Lvl) (W : List (List (List ℕ)))
    (hE : eK n (c.eW.map (evalWK n G)) = true) (hC : chainOK n C = true)
    (hg : CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G)) (inC n C (chainF C)) = true)
    (hw : wordsC n C (c.nW.map (evalWK n G)) W c.depth = true)
    (hcl : ∀ j < n, chainChunk n C (fun s => CFSG.KC.LQT.P.allL (c.nW.map (evalWK n G))
      fun g => inC n C (chainF C) (CFSG.KC.LQT.P.mul n s g)) j = true)
    (hN : normK n (c.eW.map (evalWK n G)) (c.nW.map (evalWK n G)) = true)
    (h1920 : c.nOrd % 1920 = 0)
    (hA : ∀ j < n, chainChunk n C (hypAx n (c.eW.map (evalWK n G))) j = true) :
    c.hypACheck (gs.map RN.enc) = true :=
  CFSG.KC.LQT.Syl.CoreSnd.hypAC_snd gs hG c C W hE hC hg hw hcl hN h1920 hA

end CFSG.KC.LQT.Syl

end
