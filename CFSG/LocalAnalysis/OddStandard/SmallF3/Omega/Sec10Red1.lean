module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma102_of (h33 : Asc82Lemma33) (h101 : Asc82Lemma101) : Asc82Lemma102 := by
  intro G _ _ t L hS P
  exact h33 G t L hS.toSec3SettingLB L (h101 G t L hS) (Or.inl hS.inF) P

end CFSG.OddStandard.SmallF3.Omega
