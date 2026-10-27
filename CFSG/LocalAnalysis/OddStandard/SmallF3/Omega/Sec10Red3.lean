module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIII
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma109_of (hA : Asc82Step109A) (hC : Asc82Step109C) (hD : Asc82Step109D)
    (hCor : Asc82CorIII) : Asc82Lemma109 := by
  intro G _ _ t L S z K1 K2 hctx
  by_contra hneg
  obtain ⟨g, hg⟩ := hA G t L S z K1 K2 hctx hneg
  exact hCor G t L hctx.toSec3SettingLB z (hD G t L S z K1 K2 g hg (hC G t L S z K1 K2 g hg))

end CFSG.OddStandard.SmallF3.Omega
