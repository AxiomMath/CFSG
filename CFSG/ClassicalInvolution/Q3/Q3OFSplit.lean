module

public import CFSG.ClassicalInvolution.Q3.Q3OFAlphaF

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement

section Algebra

variable {G : Type} [Group G]

theorem commute_of_commutator_mem_odd {Q : Subgroup G} (hodd : Odd (Nat.card Q)) {a l : G}
    (ha : a * a = 1) (hc : ∀ q ∈ Q, a * q = q * a) (hcomm : l * a * l⁻¹ * a⁻¹ ∈ Q) :
    l * a = a * l := by
  set d := l * a * l⁻¹ * a⁻¹ with hd
  have hda : d * a = l * a * l⁻¹ := by rw [hd]; group
  have hac : a * d = d * a := hc d hcomm
  have hsq : (d * a) * (d * a) = 1 := by
    rw [hda]
    calc l * a * l⁻¹ * (l * a * l⁻¹) = l * (a * a) * l⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have hdd : d * d = 1 := by
    calc d * d = d * d * (a * a) := by rw [ha, mul_one]
      _ = d * (d * a) * a := by simp only [mul_assoc]
      _ = d * (a * d) * a := by rw [← hac]
      _ = (d * a) * (d * a) := by simp only [mul_assoc]
      _ = 1 := hsq
  have h5 : d = 1 := eq_one_of_mul_self_eq_one_of_mem_odd hodd hcomm hdd
  have h6 : ⁅l, a⁆ = 1 := h5
  exact commutatorElement_eq_one_iff_mul_comm.mp h6

end Algebra

end CFSG.ClassicalInvolution.Q3.Q3OF
