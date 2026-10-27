module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.QuasithinUnique.K1 CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Elation

variable {F : Type} [Field F]

@[expose] def sl2Elation (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem sl2Elation_coe (t : F) :
    (sl2Elation t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem sl2Elation_add (s t : F) : sl2Elation (s + t) = sl2Elation s * sl2Elation t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Elation_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Elation_map (σ : F ≃+* F) (t : F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (sl2Elation t) = sl2Elation (σ t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Elation_coe, Matrix.SpecialLinearGroup.map_apply_coe]

@[expose] def elationHom : Multiplicative F →* SL(2, F) where
  toFun t := sl2Elation (Multiplicative.toAdd t)
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Elation_coe]
  map_mul' s t := sl2Elation_add _ _

theorem isPGroup_elation_range [CharP F 2] : IsPGroup 2 (elationHom (F := F)).range := by
  have hG : IsPGroup 2 (Multiplicative F) := by
    intro g
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [pow_one, toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  exact hG.of_surjective (elationHom (F := F)).rangeRestrict
    (elationHom (F := F)).rangeRestrict_surjective

theorem elation_commute_entries (H : SL(2, F)) (s t : F)
    (h : H * sl2Elation s = sl2Elation t * H) :
    t * (H : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (H : Matrix (Fin 2) (Fin 2) F) 0 0 * s = t * (H : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
      (H : Matrix (Fin 2) (Fin 2) F) 1 0 * s = 0 := by
  have hm := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2Elation_coe] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 : F) * e00
  · linear_combination e01
  · linear_combination e11

end Elation

section Automorphisms

variable {F : Type} [Field F]

theorem sylowCentralizingAutInner_sl2 {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    SylowCentralizingAutInner SL(2, F) := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hchar : CharP F 2 := char_two_of_card hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_elation_range (F := F))
  have hQs : IsSylowTwoOf (Q : Subgroup SL(2, F)) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨Q.isPGroup', Q.not_dvd_index⟩
  refine sylowCentralizingAutInner_of_sylow _ hQs fun β hβ => ?_
  obtain ⟨a, ha⟩ := (gammaToMulAut_bijective_of_card (F := F) hcard).2 β
  have hfix : ∀ t : F, a.left * sl2Elation (a.right t) * a.left⁻¹ = sl2Elation t := by
    intro t
    have h1 : β (sl2Elation t) = sl2Elation t := hβ _ (hQ ⟨Multiplicative.ofAdd t, rfl⟩)
    rw [← ha, gammaToMulAut_apply, sl2Elation_map] at h1
    exact h1
  have hmul : ∀ t : F, a.left * sl2Elation (a.right t) = sl2Elation t * a.left := by
    intro t
    calc a.left * sl2Elation (a.right t) = (a.left * sl2Elation (a.right t) * a.left⁻¹) * a.left := by
          group
      _ = sl2Elation t * a.left := by rw [hfix t]
  obtain ⟨h1, h2, h3⟩ := elation_commute_entries a.left (a.right 1) 1 (hmul 1)
  rw [map_one] at h2 h3
  have hdet := Matrix.det_fin_two (a.left : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.det_coe] at hdet
  have hc : (a.left : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using h1
  have hd : (a.left : Matrix (Fin 2) (Fin 2) F) 0 0 = (a.left : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simpa using h2
  have ha0 : (a.left : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    rw [hc, h0] at hdet
    simp at hdet
  have hσ : ∀ t : F, a.right t = t := by
    intro t
    obtain ⟨-, h5, -⟩ := elation_commute_entries a.left (a.right t) t (hmul t)
    rw [← hd] at h5
    exact mul_left_cancel₀ ha0 (by rw [h5]; ring)
  have hmapid : ∀ y : SL(2, F), Matrix.SpecialLinearGroup.map a.right.toRingHom y = y := by
    intro y
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, hσ]
  refine ⟨a.left⁻¹, fun y => ?_⟩
  rw [← ha, gammaToMulAut_apply, hmapid, inv_inv]

end Automorphisms

theorem sylowCentralizingAutInner_of_stated_psl_two {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : StatedClassicalModel X .PSL 2 2 f) : SylowCentralizingAutInner X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hcard
  exact SylowCentralizingAutInner.of_mulEquiv
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans sl2EquivPSL2.symm)
    (sylowCentralizingAutInner_sl2 hcard)

end CFSG.QuasithinUnique.Ch1
