module

public import Certificates.Certificate1322152

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint

private theorem exists_conj_pow_of_mul_eq {L G : Type} [Group L] [Group G] (e : L ≃* G)
    {a c : G} (ha : a ^ 31 = 1) (ha1 : a ≠ 1) (hc : c * a = a ^ 2 * c) :
    ∃ (a b : L) (k : ℕ), orderOf a = 31 ∧ b * a * b⁻¹ = a ^ k ∧
      ∀ j < 3, ¬ k ≡ 5 ^ j [MOD 31] := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine ⟨e.symm a, e.symm c, 2, ?_, ?_, by decide⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ha ha1
  · have h : c * a * c⁻¹ = a ^ 2 := by rw [hc, mul_inv_cancel_right]
    simpa only [map_mul, map_inv, map_pow] using congrArg e.symm h


theorem exists_conj_pow_thirtyOne_B {L : Type} [Group L]
    (e : L ≃* NativeSporadic.Carrier .B) :
    ∃ (a b : L) (k : ℕ), orderOf a = 31 ∧ b * a * b⁻¹ = a ^ k ∧
      ∀ j < 3, ¬ k ≡ 5 ^ j [MOD 31] := by
  obtain ⟨a, c, h1, h2, h3⟩ := Certificates.certificate1322152
  exact exists_conj_pow_of_mul_eq (G := NativeSporadic.B) e h1 h2 h3

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
