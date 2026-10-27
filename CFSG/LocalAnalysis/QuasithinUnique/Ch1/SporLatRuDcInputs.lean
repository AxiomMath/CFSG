module

public import Certificates.Data.Kernel.RuDc.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.Ru.Native (ruData)

noncomputable def ruLatK : LatData (List Nat) where
  O := default
  F := default
  sTabs := ruSTabsL
  mw := ruMw
  mt := ruMw.map fun ws => ws.map (wordTabA #[ruTaL, ruTbL] ruData.n)
  Om := #[CFSG.KD.RuDc.Om 0, CFSG.KD.RuDc.Om 1, CFSG.KD.RuDc.Om 2, CFSG.KD.RuDc.Om 3,
    CFSG.KD.RuDc.Om 4]
  atoms := #[]
  joins := []

noncomputable def ruOtK : Array (OmegaData (List (List Nat))) :=
  #[CFSG.KD.RuDc.Ot 0, CFSG.KD.RuDc.Ot 1, CFSG.KD.RuDc.Ot 2, CFSG.KD.RuDc.Ot 3, CFSG.KD.RuDc.Ot 4]

abbrev RuDcFacts : Prop :=
  (CFSG.KC.SLDc.dcCheck CFSG.KD.RuDc.C CFSG.KD.RuDc.D = true ∧ CFSG.KD.RuDc.invOK = true ∧
      CFSG.KD.RuDc.D.mw = ruMw.toList ∧
      ∀ l < 8, (ruSLPL[CFSG.KD.RuDc.nodes.getD l 0]!).size = ruData.n ∧
        ∀ p < ruData.n, (ruSLPL[CFSG.KD.RuDc.nodes.getD l 0]!).getD p 0 = CFSG.KD.RuDc.C.L l p ∧
          CFSG.KD.RuDc.C.L l p < ruData.n) ∧
    CFSG.KD.RuDc.D.sep = ruB ∧ ruLatK.sTabs = ruSTabsL ∧ ruLatK.mw = ruMw ∧
    ruLatK.Om.map (fun o => o.lbl.size) = #[1, 15, 21, 3, 3] ∧
    (List.range 5).all CFSG.KD.RuDc.memOK = true ∧
    ruOtK.map (fun o => o.lbl.size) = #[1, 8, 8, 2, 2] ∧ CFSG.KD.RuDc.inclOK = true

end CFSG.QuasithinUnique.Ch1.SporLat.RuCert
