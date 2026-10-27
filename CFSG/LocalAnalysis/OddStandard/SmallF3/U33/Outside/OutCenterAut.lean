module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutFpf

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {S : Type} [Group S]

theorem center_map_eq (α : MulAut S) : (center S).map α.toMonoidHom = center S := by
  simpa using Subgroup.map_center_eq α

@[expose] noncomputable def centerAut (α : MulAut S) : MulAut (S ⧸ center S) :=
  quotAut α (center S) (center_map_eq α)

theorem centerAut_mk (α : MulAut S) (g : S) :
    centerAut α (QuotientGroup.mk g) = QuotientGroup.mk (α g) := rfl

theorem centerAut_mul (α β : MulAut S) : centerAut (α * β) = centerAut α * centerAut β := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H g =>
    show QuotientGroup.mk ((α * β) g) = centerAut α (centerAut β (QuotientGroup.mk g))
    rw [centerAut_mk, centerAut_mk]
    rfl

theorem centerAut_one : centerAut (1 : MulAut S) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H g => rfl

theorem centerAut_inv (α : MulAut S) : centerAut α⁻¹ = (centerAut α)⁻¹ := by
  have h : centerAut α * centerAut α⁻¹ = 1 := by
    rw [← centerAut_mul, mul_inv_cancel, centerAut_one]
  exact eq_inv_of_mul_eq_one_right h

theorem centerAut_pow (α : MulAut S) (n : ℕ) : centerAut (α ^ n) = centerAut α ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, centerAut_one]
  | succ n ih => rw [pow_succ, pow_succ, centerAut_mul, ih]

theorem centerAut_fpf [Finite S] (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (v : S ⧸ center S) (hv : centerAut ρ v = v) : v = 1 := by
  exact quotAut_fpf ρ hρ hfpf (center S) (center_map_eq ρ) v hv

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
