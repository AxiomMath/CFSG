module

public import CFSG.Open.Defs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

section Alt

variable {A : Type*} [Group A] {m : ℕ}

theorem isSimpleGroup_of_alt (hm : 5 ≤ m) (e : A ≃* alternatingGroup (Fin m)) :
    IsSimpleGroup A := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  exact e.isSimpleGroup

theorem center_eq_bot_of_alt (hm : 4 ≤ m) (e : A ≃* alternatingGroup (Fin m)) :
    center A = ⊥ := by
  have h := alternatingGroup.center_eq_bot (α := Fin m) (by simpa using hm)
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ center (alternatingGroup (Fin m)) := by
    rw [mem_center_iff] at hx ⊢
    intro g
    have := hx (e.symm g)
    simpa using congrArg e this
  rw [h] at hx'
  have h1 : e x = 1 := hx'
  exact (e.injective (h1.trans (map_one e).symm))

theorem exists_two_involutions_aux {α : Type*} [DecidableEq α] [Fintype α] (p0 p1 p2 p3 : α)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h03 : p0 ≠ p3) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3)
    (h23 : p2 ≠ p3) :
    ∃ x y : alternatingGroup α,
      x ≠ y ∧ x * y = y * x ∧ orderOf x = 2 ∧ orderOf y = 2 := by
  let a : Perm α := swap p0 p1 * swap p2 p3
  let b : Perm α := swap p0 p2 * swap p1 p3
  have ha : a ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup]
    simp [a, Perm.sign_mul, Perm.sign_swap h01, Perm.sign_swap h23]
  have hb : b ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup]
    simp [b, Perm.sign_mul, Perm.sign_swap h02, Perm.sign_swap h13]
  have hab : a * b = b * a := by
    ext i
    simp only [a, b, Perm.mul_apply, swap_apply_def]
    grind
  have ha2 : a * a = 1 := by
    ext i
    simp only [a, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq]
    grind
  have hb2 : b * b = 1 := by
    ext i
    simp only [b, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq]
    grind
  have ha1 : a ≠ 1 := by
    intro h
    have := congrArg (fun f : Perm α => f p0) h
    simp only [a, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    grind
  have hb1 : b ≠ 1 := by
    intro h
    have := congrArg (fun f : Perm α => f p0) h
    simp only [b, Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    grind
  have hab' : a ≠ b := by
    intro h
    have := congrArg (fun f : Perm α => f p0) h
    simp only [a, b, Perm.mul_apply, swap_apply_def] at this
    grind
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab' (congrArg Subtype.val h), Subtype.ext hab, ?_, ?_⟩
  · apply orderOf_eq_prime
    · exact Subtype.ext (by simpa [sq] using ha2)
    · exact fun h => ha1 (congrArg Subtype.val h)
  · apply orderOf_eq_prime
    · exact Subtype.ext (by simpa [sq] using hb2)
    · exact fun h => hb1 (congrArg Subtype.val h)

theorem exists_two_involutions (hm : 4 ≤ m) :
    ∃ x y : alternatingGroup (Fin m),
      x ≠ y ∧ x * y = y * x ∧ orderOf x = 2 ∧ orderOf y = 2 :=
  exists_two_involutions_aux (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

theorem exists_two_involutions_of_alt (hm : 4 ≤ m) (e : A ≃* alternatingGroup (Fin m)) :
    ∃ x y : A, x ≠ y ∧ x * y = y * x ∧ orderOf x = 2 ∧ orderOf y = 2 := by
  obtain ⟨x, y, hxy, hcomm, hx, hy⟩ := exists_two_involutions hm
  refine ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective h), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [MulEquiv.orderOf_eq, hx]
  · rw [MulEquiv.orderOf_eq, hy]

theorem exists_noncomm_of_alt (hm : 4 ≤ m) (e : A ≃* alternatingGroup (Fin m)) :
    ∃ a b : A, a * b ≠ b * a := by
  have hc := center_eq_bot_of_alt hm e
  by_contra hcomm
  push Not at hcomm
  have hall : center A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro g
    exact hcomm g x
  rw [hc] at hall
  obtain ⟨x, y, hxy, -⟩ := exists_two_involutions_of_alt hm e
  exact hxy (by
    have hx : x ∈ (⊥ : Subgroup A) := by rw [hall]; trivial
    have hy : y ∈ (⊥ : Subgroup A) := by rw [hall]; trivial
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy])

theorem isQuasisimple_of_alt (hm : 5 ≤ m) (e : A ≃* alternatingGroup (Fin m)) :
    CFSG.Open.IsQuasisimple A := by
  have hs := isSimpleGroup_of_alt hm e
  have hc := center_eq_bot_of_alt (by omega) e
  have hnc : ¬ ∀ a b : A, a * b = b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt (by omega) e
    exact fun h => hab (h a b)
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator A) with h | h
    · exfalso
      apply hnc
      intro a b
      have h0 : a * b * a⁻¹ * b⁻¹ ∈ commutator A := by
        rw [commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h] at h0
      have h1 : a * b * a⁻¹ * b⁻¹ = 1 := h0
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot (G := A))).isSimpleGroup

end Alt

end CFSG.OddStandard.AltStdSec
