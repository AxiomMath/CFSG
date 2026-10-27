module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIII
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma105_of (hS : Asc82Step105S) (hT : Asc82Step105T) (hZ : Asc82Step105Z)
    (hCor : Asc82CorIII) : Asc82Lemma105 := by
  intro G _ _ t L S z K1 K2 hctx
  by_contra hneg
  exact hCor G t L hctx.toSec3SettingLB z
    (hZ G t L S z K1 K2 hctx (hS G t L S z K1 K2 hctx hneg) (hT G t L S z K1 K2 hctx hneg))

theorem asc82Lemma107c_of (h106 : Asc82Lemma106) (hb : Asc82Basic10) (hF : Asc82Fact107c) :
    Asc82Lemma107c := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨hpsp, -, -, -, hnorm, hsyl⟩ := hb G t L S z hctx.toSec10Z
  exact hF G t L S z K1 K2 hctx hpsp hnorm (h106 G t L S z K1 K2 hctx) hsyl

end CFSG.OddStandard.SmallF3.Omega
