module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint

theorem heldNotProperFixedInput_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput)
    (hFi : RestrictedStd.Spor.Fi24primeOuterComponentsInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (oM : CatalogueU.SporadicOddCoreFree .M) :
    GrSLit.HeldNotProperFixedInput := by
  intro S _ _ hs hna hcat σ hσ P hPF hP hPne
  have : IsSimpleGroup S := hs
  have h : ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  have hodd : OddLieType S → ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := fun ho =>
    (not_held_not_L34_of_properFixedComponent_oddLie hGLS hO hna ho h).1
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, hA⟩ | ho | he | hsp
  · obtain ⟨θ⟩ := hA
    exact not_isHeldType_of_properFixedComponent_alternating hn θ h
  · exact hodd ho
  · rcases not_isHeldType_of_properFixedComponent_evenLie hEO hO hna he h with hnh | hU
    · exact hnh
    rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
    · exact hodd ho
    · obtain ⟨θ⟩ := hA
      exact not_isHeldType_of_properFixedComponent_alternating (by omega) θ h
    · rintro ⟨eP⟩
      have h1 := card_dvd_of_fusionZStar_equiv eP.toEquiv
      rw [Sporadic.He.card_He, card_of_isL34Type hL] at h1
      norm_num at h1
    · obtain ⟨eH⟩ := hH
      exact not_isHeldType_of_properFixedComponent_held hna eH h
  · exact not_isHeldType_of_properFixedComponent_sporadic hFi hMinn hMcomp oM hna hsp h

end CFSG.ComponentClassification.CatLeaf
