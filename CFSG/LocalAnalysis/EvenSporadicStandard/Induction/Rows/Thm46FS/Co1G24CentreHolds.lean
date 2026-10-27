module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS412
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreCo1
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Induction.SporCentre


theorem co1G24Centre_holds : Co1G24Centre := by
  intro S _ _ hS hna σ hσ Q hQF hQ hQne hZ hL hCo
  obtain ⟨e⟩ := hCo
  obtain ⟨t, rfl⟩ := ComponentClassification.BMCase.inner_of_equiv e
    RankThree.PartOne.SPOR.allInner_Co1 σ
  have hPF : ComponentClassification.CatLeaf.ProperFixedComponent (MulAut.conj t) Q :=
    ⟨hσ, hQF, hQ, hQne⟩
  obtain ⟨ht2, hQC, hcomp⟩ := inner_data hna hPF hZ rfl
  have hbot : center Q = ⊥ := center_eq_bot_of_component_co1 e ht2 hQC hcomp
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hL

end CFSG.EvenSporadicStandard.Induction
