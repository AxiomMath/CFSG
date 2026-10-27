module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenAssembly
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.RestrictedStd

theorem chevalleyExceptionalModel_of_lieModel_tag {Y : Type} [Group Y] {t : StatedLieTag}
    {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel Y t 0 p f) :
    ChevalleyExceptionalModel Y t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem almostSimpleRestricted_exceptionalChevalley :
    RestrictedStd.AlmostSimpleRestricted RestrictedStd.ExceptionalChevalley := by
  intro A _ _ W _ _ _ hCW _ hP a ha L hLW _ hL hstd hsmall
  exfalso
  obtain ⟨t, p, f, ht, -, -, hm⟩ := hP
  have hW := chevalleyExceptionalModel_of_lieModel_tag ht hm
  have hNS : NoSmallComponent W := by
    by_cases hp2 : p = 2
    · subst hp2
      exact noSmallComponent_of_model_even hW
    · exact noSmallComponent_of_model_odd hp2 hW
  exact not_smallSource_of_noSmallComponent hCW ha hLW hL hstd hNS hsmall

end CFSG.ComponentClassification.ExcSelector
