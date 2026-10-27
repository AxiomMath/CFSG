module

public import CFSG.GroupTheory.PLayer.Transport

public section

namespace CFSG

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem glaPLayer_fixSubgroup_ne_bot_of_conj {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {α δ ψ : MulAut G} (h : ψ * α * ψ⁻¹ = δ)
    (hδ : GLAPLayer p (fixSubgroup δ) ≠ ⊥) : GLAPLayer p (fixSubgroup α) ≠ ⊥ := by
  have hc : MulAut.congr (ψ : G ≃* G) α = δ := by
    rw [← h]
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  exact (glaPLayer_fixSubgroup_congr_ne_bot_iff hp (ψ : G ≃* G) α).1 (hc ▸ hδ)

end CFSG

end
