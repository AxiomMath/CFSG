module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutCard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.Walter.Models

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Blueprint.NativeSporadic

theorem onOuterFixedJ1_proved :
    ONOuterFixedJ1 := by
  intro Y _ hY ν hν2 hνo
  have hG : Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.ON) := hY
  have hα : ν ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := by
    rintro ⟨y, rfl⟩
    exact hνo y rfl
  obtain ⟨e⟩ := CFSG.ComponentClassification.SolMax.nonempty_fixSub_equiv_walterJ1_of_local
    CFSG.ComponentClassification.SolMax.ONOut.onOuterLocalInput_holds hG ν hν2 hα
  exact ⟨(MulEquiv.subgroupCongr (by ext; rfl)).trans (e.trans CFSG.Walter.walterJ1EquivNative)⟩

end CFSG.EvenSporadicStandard.Solomon78
