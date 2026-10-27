module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Shape
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open Equiv Equiv.Perm

variable {N : ℕ} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}

@[expose] def pairTransp (ω : Perm (Fin N)) (a b : Fin N) : Perm (Fin N) := swap a b * swap (ω a) (ω b)

theorem swap_swap_disjoint {a b c d : Fin N} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c)
    (h4 : b ≠ d) : (swap a b).Disjoint (swap c d) := by
  intro x
  by_cases hx : x = a ∨ x = b
  · right
    rcases hx with rfl | rfl
    · exact swap_apply_of_ne_of_ne h1 h2
    · exact swap_apply_of_ne_of_ne h3 h4
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem pairTransp_even {a b : Fin N} (hab : b ≠ a) : pairTransp ω a b ∈ alternatingGroup (Fin N) := by
  rw [Perm.mem_alternatingGroup]
  unfold pairTransp
  rw [Perm.sign_mul, Perm.sign_swap (Ne.symm hab), Perm.sign_swap (fun e => hab (ω.injective e).symm)]
  decide

namespace E0Shape

variable (h : E0Shape P ω Δ₀)
include h

theorem ω_ne_self {a : Fin N} (ha : a ∉ Δ₀) : a ≠ ω a := fun e => h.ωfree a ha e.symm

theorem a_ne_ωb {a b : Fin N} (hba : b ≠ ω a) : a ≠ ω b := by
  intro e
  apply hba
  rw [e, h.ωω]

variable {a b : Fin N} (ha : a ∉ Δ₀) (hb : b ∉ Δ₀) (hab : b ≠ a) (hba : b ≠ ω a)
include ha hb hba

theorem pairTransp_comm_ω : ω * pairTransp ω a b = pairTransp ω a b * ω := by
  have hdisj : (swap (ω a) (ω b)).Disjoint (swap a b) :=
    swap_swap_disjoint (Ne.symm (h.ω_ne_self ha)) hba.symm (h.a_ne_ωb hba).symm
      (Ne.symm (h.ω_ne_self hb))
  have h1 : ω * swap a b * ω⁻¹ = swap (ω a) (ω b) := (swap_apply_apply ω a b).symm
  have h2 : ω * swap (ω a) (ω b) * ω⁻¹ = swap a b := by
    rw [← swap_apply_apply, h.ωω, h.ωω]
  have h3 : ω * pairTransp ω a b * ω⁻¹ = pairTransp ω a b := by
    unfold pairTransp
    calc ω * (swap a b * swap (ω a) (ω b)) * ω⁻¹
        = (ω * swap a b * ω⁻¹) * (ω * swap (ω a) (ω b) * ω⁻¹) := by group
      _ = swap (ω a) (ω b) * swap a b := by rw [h1, h2]
      _ = swap a b * swap (ω a) (ω b) := hdisj.commute
  calc ω * pairTransp ω a b = (ω * pairTransp ω a b * ω⁻¹) * ω := by group
    _ = pairTransp ω a b * ω := by rw [h3]

omit hb in
theorem pairTransp_apply_left : pairTransp ω a b a = b := by
  unfold pairTransp
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (h.ω_ne_self ha) (h.a_ne_ωb hba), swap_apply_left]

theorem pairTransp_apply_ωa : pairTransp ω a b (ω a) = ω b := by
  have := congrArg (fun f : Perm (Fin N) => f a) (h.pairTransp_comm_ω ha hb hba)
  simp only [Perm.mul_apply] at this
  rw [← this, h.pairTransp_apply_left ha hba]

omit hba in
theorem pairTransp_fix {y : Fin N} (hy : y ∈ Δ₀) : pairTransp ω a b y = y := by
  have h1 : y ≠ a := fun e => ha (e ▸ hy)
  have h2 : y ≠ b := fun e => hb (e ▸ hy)
  have h3 : y ≠ ω a := fun e => h.ω_not_mem ha (e ▸ hy)
  have h4 : y ≠ ω b := fun e => h.ω_not_mem hb (e ▸ hy)
  unfold pairTransp
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

end E0Shape

@[expose] def PairPerm (ω : Perm (Fin N)) (Δ₀ : Finset (Fin N)) (σ : Perm (Fin N)) : Prop :=
  (∀ y ∈ Δ₀, σ y = y) ∧ ∀ x, x ∉ Δ₀ → σ x = x ∨ σ x = ω x

namespace E0Shape

variable (h : E0Shape P ω Δ₀)
include h

theorem PairPerm.moved {σ : Perm (Fin N)} (hσ : PairPerm ω Δ₀ σ) {x : Fin N} (hx : σ x ≠ x) :
    x ∉ Δ₀ ∧ σ x = ω x ∧ σ (ω x) = x := by
  have hxΔ : x ∉ Δ₀ := fun hmem => hx (hσ.1 x hmem)
  have h1 : σ x = ω x := (hσ.2 x hxΔ).resolve_left hx
  refine ⟨hxΔ, h1, ?_⟩
  rcases hσ.2 (ω x) (h.ω_not_mem hxΔ) with h2 | h2
  · exfalso
    apply h.ωfree x hxΔ
    exact σ.injective (h2.trans h1.symm)
  · rw [h2, h.ωω]

theorem PairPerm.step {σ : Perm (Fin N)} (hσ : PairPerm ω Δ₀ σ) {x : Fin N} (hx : σ x ≠ x) :
    PairPerm ω Δ₀ (σ * swap x (ω x)) ∧ (σ * swap x (ω x)) x = x ∧
      (σ * swap x (ω x)) (ω x) = ω x ∧ ∀ j, j ≠ x → j ≠ ω x → (σ * swap x (ω x)) j = σ j := by
  obtain ⟨hxΔ, h1, h2⟩ := PairPerm.moved h hσ hx
  have hωxΔ : ω x ∉ Δ₀ := h.ω_not_mem hxΔ
  have hxne : x ≠ ω x := h.ω_ne_self hxΔ
  refine ⟨⟨fun y hy => ?_, fun z hz => ?_⟩, ?_, ?_, fun j hj1 hj2 => ?_⟩
  · have hy1 : y ≠ x := fun e => hxΔ (e ▸ hy)
    have hy2 : y ≠ ω x := fun e => hωxΔ (e ▸ hy)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy1 hy2, hσ.1 y hy]
  · by_cases hzx : z = x
    · left; rw [hzx, Perm.mul_apply, swap_apply_left, h2]
    · by_cases hzω : z = ω x
      · left
        rw [hzω, Perm.mul_apply, swap_apply_right, h1]
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzω]
        exact hσ.2 z hz
  · rw [Perm.mul_apply, swap_apply_left, h2]
  · rw [Perm.mul_apply, swap_apply_right, h1]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hj1 hj2]

theorem even_card : Even N := by
  classical
  let f : Function.End (Fin N) := fun x => ω x
  have hω : f ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    funext x
    change ω (ω x) = x
    exact h.ωω x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hω
  have hfix : f.fixedPoints = (↑Δ₀ : Set (Fin N)) := by
    ext x
    change ω x = x ↔ x ∈ Δ₀
    constructor
    · intro hx
      by_contra hn
      exact h.ωfree x hn hx
    · intro hx
      exact h.ωΔ x hx
  have hc : Nat.card f.fixedPoints = 4 := by
    rw [hfix, Nat.card_coe_set_eq, Set.ncard_coe_finset, h.card]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hmod
  have : N % 2 = 0 := by
    have := hmod
    unfold Nat.ModEq at this
    omega
  exact Nat.even_iff.2 this

end E0Shape

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
