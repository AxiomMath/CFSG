module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {S : Type} [Group S] [Finite S]

theorem card_mod_three_fix (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (H : Subgroup S)
    (hH : ∀ h ∈ H, ρ h ∈ H) : Nat.card H % 3 = Nat.card ↥(H ⊓ fixSub ρ) % 3 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun h => ⟨ρ h, hH h h.2⟩
  have hf : ∀ k : ℕ, ∀ h : H, ((f ^ k) h : S) = (ρ ^ k) h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f h) : S) = (ρ ^ k) (ρ h)
      rw [ih]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext h
    apply Subtype.ext
    rw [pow_one, hf 3 h, hρ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  have hcard : Fintype.card f.fixedPoints = Nat.card ↥(H ⊓ fixSub ρ) := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine
      { toFun := fun h => ⟨h.1.1, mem_inf.2 ⟨h.1.2, ?_⟩⟩
        invFun := fun g => ⟨⟨g.1, (mem_inf.1 g.2).1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hh : f h.1 = h.1 := Function.mem_fixedPoints_iff.mp h.2
      exact congrArg Subtype.val hh
    · apply Subtype.ext
      exact (mem_inf.1 g.2).2
    · exact fun h => Subtype.ext (Subtype.ext rfl)
    · exact fun g => Subtype.ext rfl
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact hmod

theorem exists_fixed_in_coset_of_not_dvd (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (A : Subgroup S)
    (hA : ∀ a ∈ A, ρ a ∈ A) (hcard : ¬ 3 ∣ Nat.card A) (t : S) (ht : t⁻¹ * ρ t ∈ A) :
    ∃ s : S, t⁻¹ * s ∈ A ∧ ρ s = s := by
  classical
  have hmem : ∀ s : S, t⁻¹ * s ∈ A → t⁻¹ * ρ s ∈ A := by
    intro s hs
    have h1 : t⁻¹ * ρ s = (t⁻¹ * ρ t) * ρ (t⁻¹ * s) := by
      rw [map_mul, map_inv]; group
    rw [h1]; exact mul_mem ht (hA _ hs)
  let α : Type := {s : S // t⁻¹ * s ∈ A}
  haveI : Fintype α := Fintype.ofFinite α
  let f : Function.End α := fun s => ⟨ρ s.1, hmem s.1 s.2⟩
  have hf : ∀ k : ℕ, ∀ s : α, ((f ^ k) s : S) = (ρ ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f s) : S) = (ρ ^ k) (ρ s.1)
      rw [ih]
  have hfp : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hf 3 s, hρ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hfp
  have hα : Fintype.card α = Nat.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun s => ⟨t⁻¹ * s.1, s.2⟩
        invFun := fun a => ⟨t * a.1, by simp⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun a => by apply Subtype.ext; simp }
  have hne : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    have h3 : Fintype.card α % 3 = Fintype.card f.fixedPoints % 3 := hmod
    rw [h0, hα] at h3
    simp only [Nat.zero_mod] at h3
    exact hcard (Nat.dvd_iff_mod_eq_zero.mpr h3)
  obtain ⟨⟨s, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  refine ⟨s.1, s.2, ?_⟩
  exact congrArg Subtype.val hs

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
