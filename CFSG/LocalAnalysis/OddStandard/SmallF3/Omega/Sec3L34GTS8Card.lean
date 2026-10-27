module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

def slI : SL23 := ⟨!![0, 1; 2, 0], by rw [Matrix.det_fin_two_of]; decide⟩

def slJ : SL23 := ⟨!![1, 1; 1, 2], by rw [Matrix.det_fin_two_of]; decide⟩

def slC : SL23 := ⟨!![0, 1; 2, 2], by rw [Matrix.det_fin_two_of]; decide⟩

theorem slC_cubed : slC ^ 3 = 1 := by decide +kernel

theorem slC_conj_I : slC * slI * slC⁻¹ = slJ := by decide +kernel

theorem slC_conj_J : slC * slJ * slC⁻¹ = slI * slJ := by decide +kernel

theorem slC_conj_I_sq : slC * slI ^ 2 * slC⁻¹ = slI ^ 2 := by decide +kernel

theorem slJ_conj_I : slJ * slI * slJ⁻¹ = slI⁻¹ := by decide +kernel

theorem sl23_card : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl23_rep (g : SL23) :
    ∃ a : Fin 4, ∃ b : Fin 2, ∃ t : Fin 3,
      g = slI ^ (a : ℕ) * slJ ^ (b : ℕ) * slC ^ (t : ℕ) := by
  revert g
  decide +kernel

private lemma quat_conj_pow {G : Type*} [Group G] {x y : G}
    (hx4 : x ^ 4 = 1) (hyx : y * x * y⁻¹ = x⁻¹) (m : ZMod 4) :
    y * x ^ m.val = x ^ (-m).val * y := by
  have hxinv : x⁻¹ = x ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hx4]
  have hyx' : y * x = x⁻¹ * y := by
    have := congrArg (· * y) hyx
    simpa [mul_assoc] using this
  have h2 : y * x ^ 2 = x ^ 2 * y := by
    calc y * x ^ 2 = y * x * x := by rw [pow_two]; group
      _ = (x⁻¹ * y) * x := by rw [hyx']
      _ = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x⁻¹ * y) := by rw [hyx']
      _ = (x⁻¹ * x⁻¹) * y := by group
      _ = x ^ 2 * y := by
            rw [← pow_two, inv_pow]
            exact congrArg (· * y) (show (x ^ 2)⁻¹ = x ^ 2 from by
              apply inv_eq_of_mul_eq_one_right
              rw [← pow_add]; norm_num; exact hx4)
  have h3 : y * x ^ 3 = x * y := by
    calc y * x ^ 3 = y * x ^ 2 * x := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]; group
      _ = (x ^ 2 * y) * x := by rw [h2]
      _ = x ^ 2 * (y * x) := by group
      _ = x ^ 2 * (x⁻¹ * y) := by rw [hyx']
      _ = (x ^ 2 * x⁻¹) * y := by group
      _ = x * y := by
            rw [hxinv, ← pow_add, show (2 + 3 : ℕ) = 5 by norm_num, pow_eq_pow_mod 5 hx4]
            norm_num
  have hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by revert m; decide
  rcases hm with rfl | rfl | rfl | rfl
  · simp
  · rw [show (1 : ZMod 4).val = 1 from by decide,
      show (-1 : ZMod 4).val = 3 from by decide, pow_one, ← hxinv]
    exact hyx'
  · rw [show (2 : ZMod 4).val = 2 from by decide,
      show (-2 : ZMod 4).val = 2 from by decide]
    exact h2
  · rw [show (3 : ZMod 4).val = 3 from by decide,
      show (-3 : ZMod 4).val = 1 from by decide, pow_one]
    exact h3

private lemma quat_pow_add {G : Type*} [Group G] {x : G} (hx4 : x ^ 4 = 1) :
    (∀ m n : ZMod 4, x ^ (m + n).val = x ^ m.val * x ^ n.val) ∧
      x ^ (1 : ZMod 4).val = x ∧
      x ^ (-1 : ZMod 4).val = x⁻¹ ∧
      x ^ (2 : ZMod 4).val = x ^ 2 := by
  have hxinv : x⁻¹ = x ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hx4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    rw [ZMod.val_add, ← pow_eq_pow_mod (m.val + n.val) hx4, pow_add]
  · rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]
  · rw [show (-1 : ZMod 4).val = 3 from by decide]
    exact hxinv.symm
  · rw [show (2 : ZMod 4).val = 2 from by decide]

private lemma quat_normal_form {G : Type*} [Group G] {x y : G}
    (hx4 : x ^ 4 = 1) (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    ∀ z ∈ Subgroup.closure ({x, y} : Set G),
      (∃ m : ZMod 4, z = x ^ m.val) ∨ (∃ m : ZMod 4, z = x ^ m.val * y) := by
  obtain ⟨hxP_add, hxP_one, hxP_neg_one, hxP_two⟩ := quat_pow_add hx4
  have hyxP : ∀ m : ZMod 4, y * x ^ m.val = x ^ (-m).val * y := quat_conj_pow hx4 hyx
  have hy_sq : y * y = x ^ (2 : ZMod 4).val := by rw [← pow_two, hy2, hxP_two]
  have hyinv : y⁻¹ = x ^ (2 : ZMod 4).val * y := by
    have hy4 : y ^ 4 = 1 := by
      have : y ^ 4 = (x ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hy2]
      rw [this, ← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num, hx4]
    have h : y⁻¹ = y ^ 3 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', hy4]
    calc y⁻¹ = y ^ 3 := h
      _ = y ^ 2 * y := by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
      _ = x ^ 2 * y := by rw [hy2]
      _ = x ^ (2 : ZMod 4).val * y := by rw [hxP_two]
  intro z hz
  refine Subgroup.closure_induction_left (s := ({x, y} : Set G))
    (p := fun z _ => (∃ m : ZMod 4, z = x ^ m.val) ∨ (∃ m : ZMod 4, z = x ^ m.val * y))
    (Or.inl ⟨0, by simp⟩) ?_ ?_ hz
  · intro g hg w hw ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h1 | h1
    · rw [h1]
      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inl ⟨1 + m, by rw [hxP_add, hxP_one]⟩
      · exact Or.inr ⟨1 + m, by rw [hxP_add, hxP_one]; group⟩
    · rw [h1]
      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inr ⟨-m, by rw [hyxP]⟩
      · refine Or.inl ⟨-m + 2, ?_⟩
        calc y * (x ^ m.val * y) = (y * x ^ m.val) * y := by rw [← mul_assoc]
          _ = (x ^ (-m).val * y) * y := by rw [hyxP]
          _ = x ^ (-m).val * (y * y) := by rw [mul_assoc]
          _ = x ^ (-m).val * x ^ (2 : ZMod 4).val := by rw [hy_sq]
          _ = x ^ (-m + 2).val := by rw [← hxP_add]
  · intro g hg w hw ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h1 | h1
    · rw [h1]
      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inl ⟨-1 + m, by rw [hxP_add, hxP_neg_one]⟩
      · exact Or.inr ⟨-1 + m, by rw [hxP_add, hxP_neg_one]; group⟩
    · rw [h1]
      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · refine Or.inr ⟨2 - m, ?_⟩
        calc y⁻¹ * x ^ m.val = (x ^ (2 : ZMod 4).val * y) * x ^ m.val := by rw [hyinv]
          _ = x ^ (2 : ZMod 4).val * (y * x ^ m.val) := by rw [mul_assoc]
          _ = x ^ (2 : ZMod 4).val * (x ^ (-m).val * y) := by rw [hyxP]
          _ = (x ^ (2 : ZMod 4).val * x ^ (-m).val) * y := by rw [← mul_assoc]
          _ = x ^ ((2 : ZMod 4) + -m).val * y := by rw [← hxP_add]
          _ = x ^ (2 - m).val * y := by rw [sub_eq_add_neg]
      · refine Or.inl ⟨-m, ?_⟩
        calc y⁻¹ * (x ^ m.val * y) = (x ^ (2 : ZMod 4).val * y) * (x ^ m.val * y) := by
              rw [hyinv]
          _ = x ^ (2 : ZMod 4).val * (y * x ^ m.val) * y := by group
          _ = x ^ (2 : ZMod 4).val * (x ^ (-m).val * y) * y := by rw [hyxP]
          _ = x ^ (2 : ZMod 4).val * x ^ (-m).val * (y * y) := by group
          _ = x ^ (2 : ZMod 4).val * x ^ (-m).val * x ^ (2 : ZMod 4).val := by rw [hy_sq]
          _ = x ^ ((2 : ZMod 4) + -m).val * x ^ (2 : ZMod 4).val := by rw [← hxP_add]
          _ = x ^ (((2 : ZMod 4) + -m) + 2).val := by rw [← hxP_add]
          _ = x ^ (-m).val := by
                congr 1
                have h4 : (2 : ZMod 4) + 2 = 0 := by decide
                rw [show ((2 : ZMod 4) + -m) + 2 = 2 + 2 + -m by ring, h4, zero_add]

lemma l34g_card_closure_pair_le_eight {G : Type*} [Group G] {x y : G}
    (hx4 : x ^ 4 = 1) (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 8 := by
  have hform := quat_normal_form hx4 hy2 hyx
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hsurj : Function.Surjective (fun p : ZMod 4 × ZMod 2 =>
      (⟨if p.2 = 0 then x ^ p.1.val else x ^ p.1.val * y, by
        split_ifs with h
        · exact (Subgroup.closure ({x, y} : Set G)).pow_mem hxQ p.1.val
        · exact (Subgroup.closure ({x, y} : Set G)).mul_mem
            ((Subgroup.closure ({x, y} : Set G)).pow_mem hxQ p.1.val) hyQ⟩ :
        Subgroup.closure ({x, y} : Set G))) := by
    intro z
    rcases hform z.1 z.2 with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨(m, 0), Subtype.ext ?_⟩
      show (if (0 : ZMod 2) = 0 then x ^ m.val else x ^ m.val * y) = z.1
      rw [if_pos rfl]; exact hm.symm
    · refine ⟨(m, 1), Subtype.ext ?_⟩
      show (if (1 : ZMod 2) = 0 then x ^ m.val else x ^ m.val * y) = z.1
      rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]; exact hm.symm
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  have : Nat.card (ZMod 4 × ZMod 2) = 8 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card]
  rw [this] at hcard
  exact hcard

end CFSG.OddStandard.SmallF3.Omega
