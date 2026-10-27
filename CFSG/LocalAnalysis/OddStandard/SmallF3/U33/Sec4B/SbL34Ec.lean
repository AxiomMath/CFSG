module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem eq_bot_of_normal_cyclic (R : Subgroup Λ) [R.Normal] [IsCyclic R] (r s : Λ)
    (hr3 : r ^ 3 = 1) (hs : s * r * s⁻¹ = r⁻¹)
    (hfix : ∀ x ∈ R, r * x * r⁻¹ = x → x = 1) : R = ⊥ := by
  have hcomm : ∀ a b : MulAut R, a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv R).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have h2 : s * r * s⁻¹ * r⁻¹ = r := by
    have hr2 : r ^ 2 = r⁻¹ := by
      rw [pow_two]
      exact eq_inv_of_mul_eq_one_left (by simpa [pow_three'] using hr3)
    have hsq : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
    rw [hs, hsq, hr2, inv_inv]
  have hconj : MulAut.conjNormal (H := R) r = 1 := by
    have h1 : MulAut.conjNormal (H := R) (s * r * s⁻¹ * r⁻¹ : Λ) = 1 := by
      rw [map_mul (MulAut.conjNormal (H := R)) (s * r * s⁻¹) r⁻¹,
        map_mul (MulAut.conjNormal (H := R)) (s * r) s⁻¹,
        map_mul (MulAut.conjNormal (H := R)) s r,
        map_inv (MulAut.conjNormal (H := R)) s,
        map_inv (MulAut.conjNormal (H := R)) r,
        hcomm (MulAut.conjNormal (H := R) s) (MulAut.conjNormal (H := R) r)]
      group
    rwa [h2] at h1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : MulAut.conjNormal (H := R) r ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hconj]
    exact MulAut.one_apply R ⟨x, hx⟩
  have hv := congrArg Subtype.val hx'
  rw [MulAut.conjNormal_apply] at hv
  exact hfix x hx hv

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
