module

public import CFSG.LocalAnalysis.ComponentInitial.FieldNineSymmetricSix

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Equiv Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem unique_field_nine_projective_linear_alternating_six_isomorphism (K : Type*) [Field K]
    [Fintype K] (hK : Fintype.card K = 9) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨⟨σ, hσ⟩, hΦ⟩ := unique_field_nine_semilinear_symmetric_six_isomorphism K hK
  obtain ⟨Φ, -⟩ := hΦ σ hσ
  set J := closure ((coordinateG K : Set (Perm (Omega K))) ∪ {fieldExtension K σ})
  have hGJ : coordinateG K ≤ J := fun x hx => subset_closure (Or.inl hx)
  set A : Subgroup (Perm (Fin 6)) := ((coordinateG K).subgroupOf J).map Φ.toMonoidHom
  have hAcard : Nat.card A = 360 := by
    rw [Subgroup.card_map_of_injective Φ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hGJ).toEquiv,
      FieldNine.card_coordinateG_of_card_eq_nine (by rw [Nat.card_eq_fintype_card, hK])]
  have hA : A = alternatingGroup (Fin 6) := by
    refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
    have h := A.card_mul_index
    rw [hAcard, Nat.card_perm, Nat.card_fin] at h
    have h720 : Nat.factorial 6 = 360 * 2 := by decide
    rw [h720] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  exact ⟨(pslEquivCoordinateG K).trans ((subgroupOfEquivOfLe hGJ).symm.trans
    ((((coordinateG K).subgroupOf J).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hA)))⟩

end CFSG.LocalAnalysis.ComponentInitial
