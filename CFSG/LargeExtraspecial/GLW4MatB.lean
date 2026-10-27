module

public import CFSG.LargeExtraspecial.GLW4Mat
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.GLW4

open Matrix

@[expose] def bN (u v : Fin 4 → ZMod 2) : ZMod 2 := u ⬝ᵥ (N *ᵥ v)

@[expose] def odd8 : List (Fin 4 → ZMod 2) :=
  [![0,0,1,0], ![1,1,1,0], ![1,0,1,1], ![1,1,1,1], ![1,0,1,0], ![0,1,1,0], ![0,0,1,1], ![0,1,1,1]]

@[expose] def B₁l : List (Fin 4 → ZMod 2) := [![0,0,1,0], ![1,1,1,0], ![1,0,1,1], ![1,1,1,1]]

@[expose] def B₂l : List (Fin 4 → ZMod 2) := [![1,0,1,0], ![0,1,1,0], ![0,0,1,1], ![0,1,1,1]]

@[expose] def blockCheck : Bool :=
  odd8.all fun v₀ => odd8.all fun v₁ => odd8.all fun v₂ => odd8.all fun v₃ =>
    !(decide (bN v₀ v₁ = 0) && decide (bN v₀ v₂ = 0) && decide (bN v₀ v₃ = 0) &&
      decide (bN v₁ v₂ = 0) && decide (bN v₁ v₃ = 0) && decide (bN v₂ v₃ = 0)) ||
    (decide (v₀ ∈ B₁l) && decide (v₁ ∈ B₁l) && decide (v₂ ∈ B₁l) && decide (v₃ ∈ B₁l)) ||
    (decide (v₀ ∈ B₂l) && decide (v₁ ∈ B₂l) && decide (v₂ ∈ B₂l) && decide (v₃ ∈ B₂l))

theorem blockCheck_eq : blockCheck = true := by decide +kernel

theorem mem_odd8 (v : Fin 4 → ZMod 2) (hv : bN v v = 1) : v ∈ odd8 := by
  revert v; decide

theorem orthonormal_blocks {v₀ v₁ v₂ v₃ : Fin 4 → ZMod 2} (h₀ : bN v₀ v₀ = 1)
    (h₁ : bN v₁ v₁ = 1) (h₂ : bN v₂ v₂ = 1) (h₃ : bN v₃ v₃ = 1) (h01 : bN v₀ v₁ = 0)
    (h02 : bN v₀ v₂ = 0) (h03 : bN v₀ v₃ = 0) (h12 : bN v₁ v₂ = 0) (h13 : bN v₁ v₃ = 0)
    (h23 : bN v₂ v₃ = 0) :
    (v₀ ∈ B₁l ∧ v₁ ∈ B₁l ∧ v₂ ∈ B₁l ∧ v₃ ∈ B₁l) ∨
      (v₀ ∈ B₂l ∧ v₁ ∈ B₂l ∧ v₂ ∈ B₂l ∧ v₃ ∈ B₂l) := by
  have h := blockCheck_eq
  simp only [blockCheck, List.all_eq_true] at h
  have := h v₀ (mem_odd8 v₀ h₀) v₁ (mem_odd8 v₁ h₁) v₂ (mem_odd8 v₂ h₂) v₃ (mem_odd8 v₃ h₃)
  simpa [h01, h02, h03, h12, h13, h23, and_assoc] using this

theorem bN_self (v : Fin 4 → ZMod 2) : bN v v = bN v (Pi.single 0 1) := by revert v; decide

theorem eq_zero_of_bN (x : Fin 4 → ZMod 2) (h : ∀ w, bN w x = 0) : x = 0 := by
  revert x; decide

theorem bN_sub_right (u v w : Fin 4 → ZMod 2) : bN u (v - w) = bN u v - bN u w := by
  simp [bN, mulVec_sub, dotProduct_sub]

theorem dot_mulVec_left (g : Mat) (u y : Fin 4 → ZMod 2) :
    (g *ᵥ u) ⬝ᵥ y = u ⬝ᵥ (gᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

@[expose] def IsoN (g : Mat) : Prop := gᵀ * N * g = N

theorem IsoN.bN_apply {g : Mat} (hg : IsoN g) (u v : Fin 4 → ZMod 2) :
    bN (g *ᵥ u) (g *ᵥ v) = bN u v := by
  rw [bN, bN, dot_mulVec_left, mulVec_mulVec, mulVec_mulVec, hg]

theorem IsoN.fix_e₀ {g : Mat} (hg : IsoN g) (hinv : ∃ g', g' * g = 1) :
    g *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨g', hg'⟩ := hinv
  have hgg' : g * g' = 1 := mul_eq_one_comm.mp hg'
  have key : ∀ w, bN w (g *ᵥ Pi.single 0 1 - Pi.single 0 1) = 0 := fun w => by
    have hw : w = g *ᵥ (g' *ᵥ w) := by rw [mulVec_mulVec, hgg', one_mulVec]
    rw [bN_sub_right, sub_eq_zero]
    calc bN w (g *ᵥ Pi.single 0 1) = bN (g *ᵥ (g' *ᵥ w)) (g *ᵥ Pi.single 0 1) := by rw [← hw]
      _ = bN (g' *ᵥ w) (Pi.single 0 1) := hg.bN_apply _ _
      _ = bN (g' *ᵥ w) (g' *ᵥ w) := (bN_self _).symm
      _ = bN (g *ᵥ (g' *ᵥ w)) (g *ᵥ (g' *ᵥ w)) := (hg.bN_apply _ _).symm
      _ = bN w w := by rw [← hw]
      _ = bN w (Pi.single 0 1) := bN_self w
  exact sub_eq_zero.mp (eq_zero_of_bN _ key)

theorem IsoN.maps_B₁ {g : Mat} (hg : IsoN g) :
    (∀ v ∈ B₁l, g *ᵥ v ∈ B₁l) ∨ (∀ v ∈ B₁l, g *ᵥ v ∈ B₂l) := by
  have h := orthonormal_blocks (v₀ := g *ᵥ ![0,0,1,0]) (v₁ := g *ᵥ ![1,1,1,0])
    (v₂ := g *ᵥ ![1,0,1,1]) (v₃ := g *ᵥ ![1,1,1,1])
    (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide)
    (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide)
    (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide) (by rw [hg.bN_apply]; decide)
    (by rw [hg.bN_apply]; decide)
  rcases h with ⟨h₀, h₁, h₂, h₃⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · left
    intro v hv
    simp only [B₁l, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  · right
    intro v hv
    simp only [B₁l, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption

theorem mem_B₂l_iff (v : Fin 4 → ZMod 2) : v ∈ B₂l ↔ Pi.single 0 1 + v ∈ B₁l := by
  revert v; decide

theorem add_add_cancel_vec (v w : Fin 4 → ZMod 2) : v + (v + w) = w := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem IsoN.maps_B₂_of {g : Mat} (hg : IsoN g) (hinv : ∃ g', g' * g = 1)
    (h : ∀ v ∈ B₁l, g *ᵥ v ∈ B₂l) : ∀ v ∈ B₂l, g *ᵥ v ∈ B₁l := fun w hw => by
  have hv := (mem_B₂l_iff w).mp hw
  rw [← add_add_cancel_vec (Pi.single 0 1) w, mulVec_add, hg.fix_e₀ hinv]
  exact (mem_B₂l_iff _).mp (h _ hv)

@[expose] def InK₀ (g : Mat) : Prop := ∀ v ∈ B₁l, g *ᵥ v ∈ B₁l

theorem InK₀.mul {g h : Mat} (hg : InK₀ g) (hh : InK₀ h) : InK₀ (g * h) := fun v hv => by
  rw [← mulVec_mulVec]; exact hg _ (hh v hv)

theorem IsoN.sq_mem {g : Mat} (hg : IsoN g) (hinv : ∃ g', g' * g = 1) : InK₀ (g * g) := by
  rcases hg.maps_B₁ with h | h
  · exact InK₀.mul h h
  · intro v hv
    rw [← mulVec_mulVec]
    exact hg.maps_B₂_of hinv h _ (h v hv)

theorem IsoN.of_inv {g g' : Mat} (hg : IsoN g) (hg' : g' * g = 1) : IsoN g' := by
  have h1 : g * g' = 1 := mul_eq_one_comm.mp hg'
  calc g'ᵀ * N * g' = g'ᵀ * (gᵀ * N * g) * g' := by rw [hg]
    _ = (g * g')ᵀ * N * (g * g') := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = N := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_e₂_of_mem (v : Fin 4 → ZMod 2) (h₁ : v ∈ B₁l)
    (h₂ : Pi.single 0 1 + Pi.single 1 1 + v ∈ B₁l)
    (h₃ : Pi.single 0 1 + Pi.single 3 1 + v ∈ B₁l) : v = Pi.single 2 1 := by
  revert v; decide

theorem mulVec_single_apply (g : Mat) (i j : Fin 4) : (g *ᵥ Pi.single j 1) i = g i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem InK₀.eq_one_of_fix {g : Mat} (hK : InK₀ g) (h₀ : g *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (h₁ : g *ᵥ Pi.single 1 1 = Pi.single 1 1) (h₃ : g *ᵥ Pi.single 3 1 = Pi.single 3 1) :
    g = 1 := by
  have e0 : (![0,0,1,0] : Fin 4 → ZMod 2) = Pi.single 2 1 := by decide
  have e1 : (![1,1,1,0] : Fin 4 → ZMod 2) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 := by
    decide
  have e2 : (![1,0,1,1] : Fin 4 → ZMod 2) = Pi.single 0 1 + Pi.single 3 1 + Pi.single 2 1 := by
    decide
  have m0 := hK _ (by decide : (![0,0,1,0] : Fin 4 → ZMod 2) ∈ B₁l)
  have m1 := hK _ (by decide : (![1,1,1,0] : Fin 4 → ZMod 2) ∈ B₁l)
  have m2 := hK _ (by decide : (![1,0,1,1] : Fin 4 → ZMod 2) ∈ B₁l)
  rw [e0] at m0
  rw [e1, mulVec_add, mulVec_add, h₀, h₁] at m1
  rw [e2, mulVec_add, mulVec_add, h₀, h₃] at m2
  have h₂ := eq_e₂_of_mem _ m0 m1 m2
  have hcol : ∀ j : Fin 4, g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j
    fin_cases j
    exacts [h₀, h₁, h₂, h₃]
  ext i j
  have hij := mulVec_single_apply g i j
  rw [hcol j] at hij
  rw [← hij]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

end CFSG.LargeExtraspecial.GLW4
