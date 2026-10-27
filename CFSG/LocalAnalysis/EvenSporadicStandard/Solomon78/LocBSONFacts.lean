module

public import Certificates.Certificate26682

public noncomputable section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ONSchreier

theorem on_qq :
    onq * onq = onz :=
  Certificates.certificate26682.1

theorem onz_mem_L :
    onz ∈ onL := by
  rw [← on_qq]
  exact onL.mul_mem onq_mem_L onq_mem_L

theorem on_row_facts :
    ∃ x c : Equiv.Perm (Fin N), x ∈ onL ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∉ (Subgroup.center ↥onL).map onL.subtype ∧ c ∈ Pv ∧ c * onz * c⁻¹ = onz * x ∧
      Pv ≤ onL ⊔ onL.map (MulAut.conj c).toMonoidHom ∧ OneClassOutside onL := by
  obtain ⟨-, ⟨x, c, hxL, hxx, hx1, hxc, hcP, hcz, hgen⟩, hone⟩ :=
    Certificates.certificate26682
  exact ⟨x, c, hxL, hxx, hx1, hxc, hcP, hcz, hgen, hone⟩

end CFSG.EvenSporadicStandard.Solomon78
