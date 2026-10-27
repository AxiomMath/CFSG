module

public import CFSG.GH74.QTGen4.U42.U0Core

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5

theorem perm_eq_one_of_fix_W3 : ∀ σ : Equiv.Perm (Fin 5),
    (∀ w : W3, pact σ (w : W5) = (w : W5)) → σ = 1 := by
  decide +kernel

theorem centralizer_U0_le_U0 : Subgroup.centralizer (U0 : Set Mc) ≤ U0 := by
  intro x hx
  have hc : ∀ u ∈ U0, x * u = u * x :=
    fun u hu => (Subgroup.mem_centralizer_iff.mp hx u hu).symm
  have hfix : ∀ w : W3, pact x.right (w : W5) = (w : W5) := by
    intro w
    have hu : (SemidirectProduct.inl (w : W5) : Mc) ∈ U0 := ⟨w.2, Or.inl rfl⟩
    have h := congrArg SemidirectProduct.left (hc _ hu)
    have hleft : x.left * pact x.right (w : W5) = (w : W5) * x.left := by
      simpa [SemidirectProduct.mul_left] using h
    rw [mul_comm (w : W5) x.left] at hleft
    exact mul_left_cancel hleft
  have hr : x.right = 1 := perm_eq_one_of_fix_W3 x.right hfix
  have hKfix : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → pact σ x.left = x.left := by
    intro σ hσ
    have hu : (SemidirectProduct.inr σ : Mc) ∈ U0 := ⟨W3.one_mem, hσ⟩
    have h := congrArg SemidirectProduct.left (hc _ hu)
    have hleft : x.left = pact σ x.left := by
      simpa [SemidirectProduct.mul_left] using h
    exact hleft.symm
  have hl : x.left = 1 ∨ x.left = W4 := fixed_K4 x.left hKfix
  change x.left ∈ W3 ∧ InK4 x.right
  refine ⟨?_, Or.inl hr⟩
  rcases hl with hl | hl
  · rw [hl]
    exact W3.one_mem
  · rw [hl]
    exact W4_mem_W3

end CFSG.GH74.QTGen4.U42
