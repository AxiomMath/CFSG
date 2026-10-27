module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SectionRank.Ccomm

open Matrix

theorem perfect_hom_eq_one {G M : Type*} [Group G] [Group.IsPerfect G] [CommMonoid M]
    (f : G →* M) (g : G) : f g = 1 := by
  have h := Abelianization.commutator_subset_ker f.toHomUnits
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hg : f.toHomUnits g = 1 := h (Subgroup.mem_top g)
  rw [← MonoidHom.coe_toHomUnits, hg, Units.val_one]

variable {k : Type*} [Field k]

section Matrices

theorem exists_eq_smul_one_add_smul {A B : Matrix (Fin 2) (Fin 2) k}
    (hA : ¬ ∃ c : k, A = c • 1) (hAB : A * B = B * A) : ∃ x y : k, B = x • 1 + y • A := by
  have e00 := congrFun (congrFun hAB 0) 0
  have e01 := congrFun (congrFun hAB 0) 1
  have e10 := congrFun (congrFun hAB 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases h01 : A 0 1 = 0
  · by_cases h10 : A 1 0 = 0
    · have hd : A 0 0 - A 1 1 ≠ 0 := by
        intro hd
        apply hA
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10]
        linear_combination -hd
      refine ⟨B 0 0 - (B 0 0 - B 1 1) / (A 0 0 - A 1 1) * A 0 0,
        (B 0 0 - B 1 1) / (A 0 0 - A 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10]
      · have h : B 0 1 * (A 0 0 - A 1 1) = 0 := by rw [h01] at e01; linear_combination e01
        exact (mul_eq_zero.1 h).resolve_right hd
      · have h : B 1 0 * (A 0 0 - A 1 1) = 0 := by rw [h10] at e10; linear_combination -e10
        exact (mul_eq_zero.1 h).resolve_right hd
      · field_simp
        ring
    · refine ⟨B 0 0 - B 1 0 / A 1 0 * A 0 0, B 1 0 / A 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01]
      · have h : B 0 1 * A 1 0 = 0 := by rw [h01] at e00; linear_combination -e00
        exact (mul_eq_zero.1 h).resolve_right h10
      · exact (div_mul_cancel₀ _ h10).symm
      · field_simp
        linear_combination -e10
  · refine ⟨B 0 0 - B 0 1 / A 0 1 * A 0 0, B 0 1 / A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact (div_mul_cancel₀ _ h01).symm
    · field_simp
      linear_combination e00
    · field_simp
      linear_combination e01

theorem commute_of_commute_nonscalar {A B C : Matrix (Fin 2) (Fin 2) k}
    (hA : ¬ ∃ c : k, A = c • 1) (hB : A * B = B * A) (hC : A * C = C * A) : B * C = C * B := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul hA hB
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul hA hC
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  module

theorem exists_GL_mulVec_single_eq {v : Fin 2 → k} (hv : v ≠ 0) :
    ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; v 1, 0] (by simp [h1]), ?_⟩
    ext i
    fin_cases i <;> simp [GeneralLinearGroup.mkOfDetNeZero, h0]
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [h0]), ?_⟩
    ext i
    fin_cases i <;> simp [GeneralLinearGroup.mkOfDetNeZero]

theorem eq_one_or_neg_one_of_sq_eq_one (h2 : (2 : k) ≠ 0) {g : Matrix (Fin 2) (Fin 2) k}
    (hdet : g.det = 1) (hsq : g * g = 1) : g = 1 ∨ g = -1 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e00 e01 e10 e11
  simp only [Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases htr : g 0 0 + g 1 1 = 0
  · exfalso
    apply h2
    have hd : g 1 1 = -g 0 0 := by linear_combination htr
    rw [hd] at hdet
    linear_combination -e00 - hdet
  · have hb : g 0 1 = 0 := by
      have : g 0 1 * (g 0 0 + g 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right htr
    have hc : g 1 0 = 0 := by
      have : g 1 0 * (g 0 0 + g 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right htr
    rw [hb, hc] at hdet
    rw [hb] at e00
    have ha : g 0 0 = 1 ∨ g 0 0 = -1 := by
      have : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hd : g 1 1 = g 0 0 := by
      rcases ha with ha | ha <;> rw [ha] at hdet ⊢
      · linear_combination hdet
      · linear_combination -hdet
    rcases ha with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

end Matrices

variable (J : Subgroup (GL (Fin 2) k))

theorem det_eq_one_of_perfect [Group.IsPerfect J] {g : GL (Fin 2) k} (hg : g ∈ J) :
    (g : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  have h := perfect_hom_eq_one (GeneralLinearGroup.det.comp J.subtype) ⟨g, hg⟩
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype] at h
  have := congrArg Units.val h
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem perfect_eq_bot_of_upper [Group.IsPerfect J]
    (h : ∀ g ∈ J, (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) : J = ⊥ := by
  have hmul : ∀ a b : J, (((a * b : J) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((a : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((b : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := fun _ _ => rfl
  let χ₀ : J →* k :=
    { toFun := fun g => ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0
      map_one' := by simp
      map_mul' := fun a b => by
        rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, h b b.2, mul_zero, add_zero] }
  let χ₁ : J →* k :=
    { toFun := fun g => ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1
      map_one' := by simp
      map_mul' := fun a b => by
        rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, h a a.2, zero_mul, zero_add] }
  have h0 : ∀ g : J, ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 :=
    perfect_hom_eq_one χ₀
  have h1 : ∀ g : J, ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 :=
    perfect_hom_eq_one χ₁
  have hcomm : ∀ a b : J, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Units.ext
    change ((a : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((b : GL (Fin 2) k) : Matrix _ _ k) =
      ((b : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((a : GL (Fin 2) k) : Matrix _ _ k)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h a a.2, h b b.2, h0, h1, add_comm]
  have : IsMulCommutative J := ⟨⟨hcomm⟩⟩
  have : Subsingleton J := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact Subgroup.eq_bot_of_subsingleton J

theorem perfect_no_common_eigenvector [Group.IsPerfect J] (hJ : J ≠ ⊥) {v : Fin 2 → k}
    (hv : v ≠ 0) : ∃ g ∈ J, ∀ c : k, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ≠ c • v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hP⟩ := exists_GL_mulVec_single_eq hv
  set J' := J.map (MulAut.conj P⁻¹).toMonoidHom with hJ'
  have hup : ∀ g ∈ J', (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := hcon g hg
    have hmv : ((MulAut.conj P⁻¹ g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ
        Pi.single 0 1 = c • Pi.single 0 1 := by
      rw [MulAut.conj_apply, inv_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hP, hc, Matrix.mulVec_smul, ← hP, Matrix.mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have h1 := congrFun hmv 1
    simpa [Matrix.mulVec_single_one] using h1
  have : Group.IsPerfect J' := Group.IsPerfect.map _
  have hbot : J' = ⊥ := perfect_eq_bot_of_upper J' hup
  apply hJ
  rw [hJ', Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at hbot
  exact hbot

theorem perfect_mem_center_iff [Group.IsPerfect J] (hJ : J ≠ ⊥) (g : J) :
    g ∈ Subgroup.center J ↔ ∃ c : k, ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = c • 1 := by
  constructor
  · intro hg
    by_contra hns
    have hcomm : ∀ a b : J, a * b = b * a := by
      intro a b
      have ha := Subgroup.mem_center_iff.1 hg a
      have hb := Subgroup.mem_center_iff.1 hg b
      apply Subtype.ext
      apply Units.ext
      exact commute_of_commute_nonscalar hns
        (congrArg (fun x : J => ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) ha).symm
        (congrArg (fun x : J => ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) hb).symm
    have : IsMulCommutative J := ⟨⟨hcomm⟩⟩
    have : Subsingleton J := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact hJ (Subgroup.eq_bot_of_subsingleton J)
  · rintro ⟨c, hc⟩
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply Units.ext
    change ((h : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((g : GL (Fin 2) k) : Matrix _ _ k) =
      ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((h : GL (Fin 2) k) : Matrix _ _ k)
    rw [hc, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem perfect_center_eq_one_or_neg_one [Group.IsPerfect J] (hJ : J ≠ ⊥) {g : J}
    (hg : g ∈ Subgroup.center J) : (g : GL (Fin 2) k) = 1 ∨ (g : GL (Fin 2) k) = -1 := by
  obtain ⟨c, hc⟩ := (perfect_mem_center_iff J hJ g).1 hg
  have hdet := det_eq_one_of_perfect J g.2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 hc2 with h | h
  · left
    apply Units.ext
    rw [hc, Units.val_one, show c = 1 by linear_combination h, one_smul]
  · right
    apply Units.ext
    rw [hc, Units.val_neg, Units.val_one, show c = -1 by linear_combination h, neg_one_smul]

theorem perfect_linear_two_basics [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    (∀ g ∈ J, (g : Matrix (Fin 2) (Fin 2) k).det = 1) ∧
      (∀ v : Fin 2 → k, v ≠ 0 →
        ∃ g ∈ J, ∀ c : k, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ≠ c • v) ∧
      (∀ g : J, g ∈ Subgroup.center J ↔
        ∃ c : k, ((g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = c • 1) ∧
      Nat.card (Subgroup.center J) ≤ 2 := by
  refine ⟨fun g hg => det_eq_one_of_perfect J hg, fun v hv => perfect_no_common_eigenvector J hJ hv,
    perfect_mem_center_iff J hJ, ?_⟩
  classical
  let f : Subgroup.center J → ({1, -1} : Finset (GL (Fin 2) k)) := fun z =>
    ⟨((z : J) : GL (Fin 2) k), by
      rcases perfect_center_eq_one_or_neg_one J hJ z.2 with h | h <;> simp [h]⟩
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card (Subgroup.center J) ≤ Nat.card ({1, -1} : Finset (GL (Fin 2) k)) :=
        Nat.card_le_card_of_injective f hf
    _ = Finset.card ({1, -1} : Finset (GL (Fin 2) k)) := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

end CFSG.SectionRank.Ccomm
