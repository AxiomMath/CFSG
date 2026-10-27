module

public import CFSG.LargeExtraspecial.SL4ModNorm
public import CFSG.LargeExtraspecial.SL4ModWeyl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (σ : SL4 →* (W ≃ₗ[ZMod 2] W))

theorem add_self_eq_zero' (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_of_add_eq_zero' {x y : W} (h : x + y = 0) : x = y := by
  rw [add_eq_zero_iff_eq_neg] at h
  rw [h, neg_eq_of_add_eq_zero_left (add_self_eq_zero' y)]

@[expose] def IsFixU (y : W) : Prop := ∀ u ∈ U, σ u y = y

@[expose] def heckeN (i : ℕ) (y : W) : W := σ (genN (i + 3)) y + σ (genN i * genN (i + 3)) y

theorem mul_nn_nn (i : Fin 3) (a : SL4) : a * nn i * nn i = a := by
  rw [mul_assoc, nn_mul_self, mul_one]

theorem heckeN_eq (i : Fin 3) (y : W) : heckeN σ i.val y = σ (nn i) y + σ (xx i * nn i) y := rfl

theorem heckeN_isFixU (i : Fin 3) {y : W} (hy : IsFixU σ y) : IsFixU σ (heckeN σ i.val y) := by
  intro u hu
  rw [heckeN_eq, map_add, ← act_mul, ← act_mul]
  rcases coset_cases i hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : u * nn i = nn i * (nn i * u * nn i) := by
      simp only [← mul_assoc, nn_mul_self, one_mul]
    have e2 : u * (xx i * nn i) = xx i * nn i * (nn i * xx i * u * xx i * nn i) := by
      simp only [← mul_assoc, mul_nn_nn, xx_mul_self, one_mul]
    rw [e1, e2, act_mul, hy _ h1, act_mul σ (xx i * nn i), hy _ h2]
  · have e1 : u * nn i = xx i * nn i * (nn i * xx i * u * nn i) := by
      simp only [← mul_assoc, mul_nn_nn, xx_mul_self, one_mul]
    have e2 : u * (xx i * nn i) = nn i * (nn i * u * xx i * nn i) := by
      simp only [← mul_assoc, nn_mul_self, one_mul]
    rw [e1, e2, act_mul σ (xx i * nn i), hy _ h1, act_mul σ (nn i), hy _ h2, add_comm]

theorem nn_isFixU_of_heckeN_eq_zero (i : Fin 3) {y : W} (hy : IsFixU σ y)
    (hT : heckeN σ i.val y = 0) : IsFixU σ (σ (nn i) y) := by
  rw [heckeN_eq] at hT
  have hxn := (eq_of_add_eq_zero' hT).symm
  intro u hu
  rw [← act_mul]
  rcases coset_cases i hu with ⟨h1, -⟩ | ⟨h1, -⟩
  · have e1 : u * nn i = nn i * (nn i * u * nn i) := by
      simp only [← mul_assoc, nn_mul_self, one_mul]
    rw [e1, act_mul, hy _ h1]
  · have e1 : u * nn i = xx i * nn i * (nn i * xx i * u * nn i) := by
      simp only [← mul_assoc, mul_nn_nn, xx_mul_self, one_mul]
    rw [e1, act_mul σ (xx i * nn i), hy _ h1, hxn]

theorem exists_fixed_of_heckeN_eq_zero (i : Fin 3) {y : W} (hy : IsFixU σ y) (hy0 : y ≠ 0)
    (hT : heckeN σ i.val y = 0) : ∃ w : W, w ≠ 0 ∧ σ (nn i) w = w ∧ IsFixU σ w := by
  have hz := nn_isFixU_of_heckeN_eq_zero σ i hy hT
  by_cases hw : y + σ (nn i) y = 0
  · refine ⟨y, hy0, (eq_of_add_eq_zero' hw).symm, hy⟩
  · refine ⟨y + σ (nn i) y, hw, ?_, fun u hu => ?_⟩
    · rw [map_add, ← act_mul, nn_mul_self, act_one, add_comm]
    · rw [map_add, hy u hu, hz u hu]

@[expose] def heckeW : List ℕ → W → W
  | [] => id
  | i :: ws => fun y => heckeN σ i (heckeW ws y)

theorem heckeW_eq_sum (ws : List ℕ) (y : W) :
    heckeW σ ws y = ((gList ws).map fun g => σ g y).sum := by
  induction ws with
  | nil =>
    change y = [σ 1 y].sum
    rw [List.sum_singleton, act_one]
  | cons i ws ih =>
    change heckeN σ i (heckeW σ ws y) = _
    rw [ih, heckeN, map_list_sum, map_list_sum, gList, List.map_append, List.sum_append,
      List.map_map, List.map_map, List.map_map, List.map_map]
    have f1 : (⇑(σ (genN (i + 3))) ∘ fun g => σ g y) =
        (fun g => σ g y) ∘ fun g => genN (i + 3) * g := by
      funext g
      simp only [Function.comp_apply, act_mul]
    have f2 : (⇑(σ (genN i * genN (i + 3))) ∘ fun g => σ g y) =
        (fun g => σ g y) ∘ fun g => genN i * genN (i + 3) * g := by
      funext g
      simp only [Function.comp_apply, act_mul]
    rw [f1, f2]

theorem heckeW_w0 [FiniteDimensional (ZMod 2) W] (h64 : finrank (ZMod 2) W < 64) (y : W) :
    heckeW σ w0 y = 0 := by
  let _ : Fintype U := Fintype.ofFinite U
  rw [heckeW_eq_sum]
  have e : (fun g => σ g y) = fun g => σ (g * nw0) (σ nw0 y) := by
    funext g
    rw [← act_mul, mul_assoc, nw0_mul_self, mul_one]
  rw [e, ← sum_U_eq (fun g => σ g (σ nw0 y))]
  have hcard : Fintype.card U = 64 := by rw [← Nat.card_eq_fintype_card, natCard_U]
  exact sum_apply_eq_zero isPGroup_U (σ.comp U.subtype) (by rw [hcard]; exact h64) _

theorem heckeW_isFixU {ws : List ℕ} (hws : ∀ i ∈ ws, i < 3) {y : W} (hy : IsFixU σ y) :
    IsFixU σ (heckeW σ ws y) := by
  induction ws with
  | nil => exact hy
  | cons i ws ih =>
    exact heckeN_isFixU σ ⟨i, hws i (by simp)⟩ (ih fun j hj => hws j (List.mem_cons_of_mem i hj))

theorem exists_heckeN_eq_zero {ws : List ℕ} (hws : ∀ i ∈ ws, i < 3) {y : W} (hy : IsFixU σ y)
    (hy0 : y ≠ 0) (h : heckeW σ ws y = 0) :
    ∃ i : Fin 3, ∃ y' : W, IsFixU σ y' ∧ y' ≠ 0 ∧ heckeN σ i.val y' = 0 := by
  induction ws with
  | nil => exact absurd h hy0
  | cons i ws ih =>
    have hws' : ∀ j ∈ ws, j < 3 := fun j hj => hws j (List.mem_cons_of_mem i hj)
    by_cases h0 : heckeW σ ws y = 0
    · exact ih hws' h0
    · exact ⟨⟨i, hws i (by simp)⟩, heckeW σ ws y, heckeW_isFixU σ hws' hy, h0, h⟩

theorem exists_fixed_parabolic [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    (h64 : finrank (ZMod 2) W < 64) :
    ∃ i : Fin 3, ∃ w : W, w ≠ 0 ∧ σ (nn i) w = w ∧ ∀ u ∈ U, σ u w = w := by
  obtain ⟨y, hy0, hy⟩ := exists_fixed_ne_zero isPGroup_U (σ.comp U.subtype)
  have hyU : IsFixU σ y := fun u hu => hy ⟨u, hu⟩
  obtain ⟨i, y', hy', hy'0, hT⟩ :=
    exists_heckeN_eq_zero σ (ws := w0) (by decide) hyU hy0 (heckeW_w0 σ h64 y)
  obtain ⟨w, hw0, hwn, hwU⟩ := exists_fixed_of_heckeN_eq_zero σ i hy' hy'0 hT
  exact ⟨i, w, hw0, hwn, hwU⟩

end CFSG.LargeExtraspecial.SL4Mod
