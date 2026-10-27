module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoModelMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateSemilinear

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Equiv

section Three

theorem translation_one_zmod3 :
    translation (ZMod 3) 1 = swap (some 0) (some 1) * swap (some 1) (some 2) := by
  refine Equiv.ext fun x => ?_
  rcases x with _ | x
  · rfl
  · fin_cases x <;> decide

theorem translation_two_zmod3 :
    translation (ZMod 3) 2 = swap (some 0) (some 2) * swap (some 2) (some 1) := by
  refine Equiv.ext fun x => ?_
  rcases x with _ | x
  · rfl
  · fin_cases x <;> decide

theorem inversion_zmod3 :
    inversion (ZMod 3) = swap none (some 0) * swap (some 1) (some 2) := by
  refine Equiv.ext fun x => ?_
  rcases x with _ | x
  · rw [inversion_none]
    decide
  · rcases (by decide : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = 2) x with rfl | rfl | rfl
    · rw [inversion_zero]
      decide
    · rw [inversion_nonzero _ _ (by decide), inv_one]
      decide
    · rw [inversion_nonzero _ _ (by decide),
        show (2 : ZMod 3)⁻¹ = 2 from inv_eq_of_mul_eq_one_right (by decide)]
      decide

theorem multiplier_neg_one_zmod3 :
    multiplier (ZMod 3) (-1) = swap (some 1) (some 2) := by
  refine Equiv.ext fun x => ?_
  rcases x with _ | x
  · rfl
  · fin_cases x <;> decide

theorem sign_swap_mul_swap {α : Type*} [DecidableEq α] [Fintype α] {a b c d : α} (hab : a ≠ b)
    (hcd : c ≠ d) : Perm.sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  decide

theorem coordinateG_zmod3_le_alternatingGroup :
    coordinateG (ZMod 3) ≤ alternatingGroup (Omega (ZMod 3)) := by
  rw [coordinateG, Subgroup.closure_le]
  rintro g (⟨b, rfl⟩ | hg)
  · fin_cases b
    · change translation (ZMod 3) 0 ∈ alternatingGroup _
      have : translation (ZMod 3) 0 = 1 := Equiv.ext fun x => by cases x <;> simp
      rw [this]
      exact one_mem _
    · change translation (ZMod 3) 1 ∈ alternatingGroup _
      rw [Equiv.Perm.mem_alternatingGroup, translation_one_zmod3]
      exact sign_swap_mul_swap (by decide) (by decide)
    · change translation (ZMod 3) 2 ∈ alternatingGroup _
      rw [Equiv.Perm.mem_alternatingGroup, translation_two_zmod3]
      exact sign_swap_mul_swap (by decide) (by decide)
  · rw [Set.mem_singleton_iff] at hg
    rw [hg, SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, inversion_zmod3]
    exact sign_swap_mul_swap (by decide) (by decide)

theorem coordinateG_zmod3_eq_alternatingGroup :
    coordinateG (ZMod 3) = alternatingGroup (Omega (ZMod 3)) := by
  refine Subgroup.eq_of_le_of_card_ge coordinateG_zmod3_le_alternatingGroup ?_
  rw [← Nat.card_congr (pslEquivCoordinateG (ZMod 3)).toEquiv, nat_card_psl2_zmod3,
    nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]
  decide


theorem coordinateD_zmod3_eq_top : coordinateD (ZMod 3) = ⊤ := by
  have hμ : multiplier (ZMod 3) (-1) ∈ coordinateD (ZMod 3) :=
    Subgroup.subset_closure (Or.inr ⟨-1, rfl⟩)
  have hμsign : Perm.sign (multiplier (ZMod 3) (-1)) = -1 := by
    rw [multiplier_neg_one_zmod3, Perm.sign_swap (by decide)]
  have hAlt : alternatingGroup (Omega (ZMod 3)) ≤ coordinateD (ZMod 3) := by
    rw [← coordinateG_zmod3_eq_alternatingGroup]
    exact coordinateG_le_D (ZMod 3)
  rw [eq_top_iff]
  intro g _
  by_cases hg : Perm.sign g = 1
  · exact hAlt (Perm.mem_alternatingGroup.mpr hg)
  · have hg' : Perm.sign g = -1 := (Int.units_eq_one_or g.sign).resolve_left hg
    have hmem : g * (multiplier (ZMod 3) (-1))⁻¹ ∈ coordinateD (ZMod 3) := by
      apply hAlt
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hg', hμsign]
      decide
    simpa using (coordinateD (ZMod 3)).mul_mem hmem hμ

theorem coordinateE_zmod3_eq_top : coordinateE (ZMod 3) = ⊤ :=
  eq_top_iff.mpr (coordinateD_zmod3_eq_top ▸ coordinateD_le_E (ZMod 3))

theorem three_element_field_projective_actions :
    Nat.card (Omega (ZMod 3)) = 4 ∧
      coordinateG (ZMod 3) = alternatingGroup (Omega (ZMod 3)) ∧
      coordinateD (ZMod 3) = ⊤ ∧ coordinateE (ZMod 3) = ⊤ ∧
      ∀ (X : Type*) [Fintype X] [DecidableEq X], Fintype.card X = 4 →
        ∀ (H : Type*) [Group H], Nonempty (H ≃* alternatingGroup X) ∨ Nonempty (H ≃* Perm X) →
          ∃ S : Subgroup (Perm (Omega (ZMod 3))), coordinateG (ZMod 3) ≤ S ∧
            S ≤ coordinateE (ZMod 3) ∧ Nonempty (H ≃* S) := by
  have hcard : Nat.card (Omega (ZMod 3)) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]
  refine ⟨hcard, coordinateG_zmod3_eq_alternatingGroup, coordinateD_zmod3_eq_top,
    coordinateE_zmod3_eq_top, fun X _ _ hX H _ hH => ?_⟩
  have e : X ≃ Omega (ZMod 3) :=
    Fintype.equivOfCardEq (by rw [hX, ← Nat.card_eq_fintype_card, hcard])
  rcases hH with hφ | hφ
  · obtain ⟨φ⟩ := hφ
    refine ⟨coordinateG (ZMod 3), le_rfl, (coordinateG_le_D _).trans (coordinateD_le_E _), ?_⟩
    exact ⟨(φ.trans e.altCongrHom).trans
      (MulEquiv.subgroupCongr coordinateG_zmod3_eq_alternatingGroup.symm)⟩
  · obtain ⟨φ⟩ := hφ
    refine ⟨coordinateE (ZMod 3), (coordinateG_le_D _).trans (coordinateD_le_E _), le_rfl, ?_⟩
    exact ⟨((φ.trans e.permCongrHom).trans Subgroup.topEquiv.symm).trans
      (MulEquiv.subgroupCongr coordinateE_zmod3_eq_top.symm)⟩

end Three

section Five

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem five_field_linear_two_alternating_five_model
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 5) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) ∧
      ∀ (Y : Type) [Group Y], Nonempty (Y ≃* alternatingGroup (Fin 5)) →
        @ComponentType.ClassicalModel Y _ .PSL 2 5 1 ⟨Nat.prime_five⟩ ∧
          ComponentType.OddLieType Y := by
  have hP : ∀ (L : Type) [Field L] [Finite L], Nat.card L = 5 →
      Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) L ≃* alternatingGroup (Fin 5)) := by
    intro L _ _ hL
    obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five L
      (Or.inr hL)
    exact ⟨(projectiveSpecialLinearGroupEquivStatedProj 2 L).trans e⟩
  refine ⟨hP K hK, fun Y _ ⟨eY⟩ => ?_⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hGF : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 one_ne_zero, pow_one]
  obtain ⟨eGF⟩ := hP (GaloisField 5 1) hGF
  have hmodel : ComponentType.ClassicalModel Y .PSL 2 5 1 := by
    refine ⟨?_, ⟨(eY.trans eGF.symm).trans
      (CFSG.ComponentClassification.CatalogueBLinearTwoModel.nativePSLEquivPslModel 5 1)⟩⟩
    show Nat.Prime 5 ∧ 1 ≤ 1 ∧ 2 ≤ 2 ∧ ¬(2 = 2 ∧ (5 ^ 1 = 2 ∨ 5 ^ 1 = 3))
    exact ⟨Nat.prime_five, le_rfl, le_rfl, by norm_num⟩
  exact ⟨hmodel, Or.inl ⟨.PSL, 2, 5, 1, inferInstance, by decide, hmodel⟩⟩

end Five

end CFSG.LinearGroups
