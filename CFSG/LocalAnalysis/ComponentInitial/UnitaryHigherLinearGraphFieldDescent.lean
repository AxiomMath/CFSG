module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open LinearFlag

theorem linear_graph_field_involution_descent {K : Type} [Field K] {n p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    Even f ∧ (∀ x, σ x = x ^ p ^ (f / 2)) ∧
      ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ * dualAut n K =
        conjAut n K H * (fieldAut n K σ * dualAut n K) * (conjAut n K H)⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  exact odd_linear_graph_field_involution_conjugacy hp hf hK hn A σ hσ hα

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
