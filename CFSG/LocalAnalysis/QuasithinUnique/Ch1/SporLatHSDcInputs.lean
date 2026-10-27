module

public import Certificates.Data.Kernel.HSDc.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.HS.Native (hsData)

noncomputable def hsLatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := hsSTabs
  mw := CFSG.KD.HSDc.J.mw.toArray
  mt := CFSG.KD.HSDc.J.mw.toArray.map fun ws => ws.map (wordTabA #[hsTa, hsTb] hsData.n)
  Om := #[CFSG.KD.HSDc.Om 0, CFSG.KD.HSDc.Om 1, CFSG.KD.HSDc.Om 2, CFSG.KD.HSDc.Om 3,
    CFSG.KD.HSDc.Om 4]
  atoms := #[]
  joins := []

noncomputable def hsOtK : Array (OmegaData (List (List ℕ))) :=
  #[CFSG.KD.HSDc.Ot 0, CFSG.KD.HSDc.Ot 1, CFSG.KD.HSDc.Ot 2, CFSG.KD.HSDc.Ot 3, CFSG.KD.HSDc.Ot 4]

abbrev HSDcFacts : Prop :=
  CFSG.KC.SLDc.dcCheck CFSG.KD.HSDc.C CFSG.KD.HSDc.D = true ∧ CFSG.KD.HSDc.invOK = true ∧
    (∀ l < 8, ∀ p < hsData.n,
      (hsSLP[CFSG.KD.HSDc.nodes.getD l 0]!).getD p 0 = CFSG.KD.HSDc.C.L l p ∧
        CFSG.KD.HSDc.C.L l p < hsData.n) ∧
    CFSG.KD.HSDc.J.sep = hsB ∧ CFSG.KD.HSDc.mwOK = true ∧ CFSG.KD.HSDc.J.mw.length = 5 ∧
    CFSG.KD.HSDc.J.mw.getD 0 [] = [] ∧
    hsLatK.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] ∧
    (List.range 5).all CFSG.KD.HSDc.memOK = true ∧
    hsOtK.map (fun o => o.lbl.size) = #[1, 8, 8, 2, 2]

end CFSG.QuasithinUnique.Ch1.SporLat.HS
