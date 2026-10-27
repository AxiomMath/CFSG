module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

variable {T : Type} [Group T] [Finite T]

theorem map_eq_self (N : Subgroup T) (α : MulAut T) (hN : ∀ n ∈ N, α n ∈ N) :
    N.map (α : T →* T) = N := by
  have hle : N.map (α : T →* T) ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact hN n hn
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective α.injective).symm)

@[expose] def quotAut (N : Subgroup T) [N.Normal] (α : MulAut T) (hN : ∀ n ∈ N, α n ∈ N) :
    MulAut (T ⧸ N) :=
  QuotientGroup.congr N N α (map_eq_self N α hN)

theorem quotAut_mk (N : Subgroup T) [N.Normal] (α : MulAut T) (hN : ∀ n ∈ N, α n ∈ N) (g : T) :
    quotAut N α hN (QuotientGroup.mk g) = QuotientGroup.mk (α g) :=
  QuotientGroup.congr_mk N N α _ g

theorem quotAut_pow_mk (N : Subgroup T) [N.Normal] (α : MulAut T) (hN : ∀ n ∈ N, α n ∈ N)
    (n : ℕ) (g : T) :
    ((quotAut N α hN) ^ n) (QuotientGroup.mk g) = QuotientGroup.mk ((α ^ n) g) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, quotAut_mk, ih]

theorem quotAut_pow_eq_one (N : Subgroup T) [N.Normal] (α : MulAut T) (hN : ∀ n ∈ N, α n ∈ N)
    (n : ℕ) (h : α ^ n = 1) : (quotAut N α hN) ^ n = 1 := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [quotAut_pow_mk, h]
    rfl

theorem quotAut_comm (N : Subgroup T) [N.Normal] (α β : MulAut T) (hα : ∀ n ∈ N, α n ∈ N)
    (hβ : ∀ n ∈ N, β n ∈ N) (h : α * β = β * α) :
    quotAut N α hα * quotAut N β hβ = quotAut N β hβ * quotAut N α hα := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [MulAut.mul_apply, MulAut.mul_apply, quotAut_mk, quotAut_mk, quotAut_mk, quotAut_mk]
    have := congrArg (fun s : MulAut T => s g) h
    simp only [MulAut.mul_apply] at this
    rw [this]

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
