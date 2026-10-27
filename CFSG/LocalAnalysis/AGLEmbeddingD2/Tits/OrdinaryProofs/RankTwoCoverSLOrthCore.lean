module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthPow

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthCore

open Matrix CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthPow

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [Field R]

public theorem trace_conj (g : Matrix.SpecialLinearGroup ι R) (X : Matrix ι ι R) :
    trace ((g : Matrix ι ι R) * X * ((g⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R)) =
      trace X := by
  have hinv : ((g⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) * (g : Matrix ι ι R) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [trace_mul_comm, ← mul_assoc, hinv, one_mul]

public theorem coe_mul_inv_self (g : Matrix.SpecialLinearGroup ι R) :
    (g : Matrix ι ι R) * ((g⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

public theorem pow_mod_three_matrix {M : Matrix ι ι R} (hM3 : M ^ 3 = 1) (n : ℕ) :
    M ^ n = M ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, hM3, one_pow, one_mul]

public theorem not_conj_core (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q)
    (u T : Matrix.SpecialLinearGroup ι R)
    (hu : (u : Matrix ι ι R) = 1 + Sx R p q)
    (hu3 : u ^ 3 = 1)
    (hT1 : (T : Matrix ι ι R) ≠ 1)
    (hTtr : trace (T : Matrix ι ι R) ≠ trace (1 + Sx R p q))
    (g : Matrix.SpecialLinearGroup ι R) (e : ℕ) : g * u ^ e * g⁻¹ ≠ T := by
  intro h
  have hM3 : (u : Matrix ι ι R) ^ 3 = 1 := by
    have := congrArg Subtype.val hu3
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hcoe : (g : Matrix ι ι R) * ((u : Matrix ι ι R) ^ e) *
      ((g⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) = (T : Matrix ι ι R) := by
    have := congrArg Subtype.val h
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using this
  rw [pow_mod_three_matrix hM3 e] at hcoe
  have hM2 : (u : Matrix ι ι R) ^ 2 = 1 + Sx R p q * Sx R p q := by
    rw [pow_two, hu]
    have e1 : (1 + Sx R p q) * (1 + Sx R p q) = 1 + (Sx R p q + Sx R p q) + Sx R p q * Sx R p q := by
      noncomm_ring
    rw [e1, dbl_mat h2, add_zero]
  have hM2tr : trace ((u : Matrix ι ι R) ^ 2) = trace (1 + Sx R p q) := by
    rw [hM2]
    simp only [trace_add, trace_one, trace_Sx_mul_Sx h2 hpq, trace_Sx p q hpq]
  have hgg := coe_mul_inv_self g
  obtain h0 | h1 | h2' : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  · rw [h0, pow_zero, mul_one, hgg] at hcoe
    exact hT1 hcoe.symm
  · rw [h1, pow_one] at hcoe
    have h := trace_conj g (u : Matrix ι ι R)
    rw [hcoe] at h
    exact hTtr (h.trans (congrArg trace hu))
  · rw [h2'] at hcoe
    have h := trace_conj g ((u : Matrix ι ι R) ^ 2)
    rw [hcoe] at h
    exact hTtr (h.trans hM2tr)

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthCore
