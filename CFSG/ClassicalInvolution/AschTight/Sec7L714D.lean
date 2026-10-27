module

public import CFSG.ClassicalInvolution.AschTight.Sec7Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) x

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
