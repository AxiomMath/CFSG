module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem char_prime_power_eq_one {field : Type u} [Field field]
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (member : field) (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1) : member = 1 := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hzero : (member - 1) ^ (prime ^ exponent) = 0 := by
    rw [sub_pow_char_pow, hpower, one_pow, sub_self]
  have hbase : member - 1 = 0 := eq_zero_of_pow_eq_zero hzero
  exact sub_eq_zero.mp hbase

theorem one_dimensional_linear_pElement_eq_one {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (hdimension : Module.finrank field space = 1) (equivalence : space ≃ₗ[field] space)
    (exponent : ℕ) (hpower : equivalence ^ (prime ^ exponent) = 1) : equivalence = 1 := by
  obtain ⟨basisVector, hvectorNe, hspan⟩ := finrank_eq_one_iff'.mp hdimension
  obtain ⟨scalar, hscalar⟩ := hspan (equivalence basisVector)
  have hiterate : ∀ power : ℕ, (equivalence ^ power) basisVector = scalar ^ power • basisVector := by
    intro power
    induction power with
    | zero => simp
    | succ power ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, ← hscalar, smul_smul, ← pow_succ]
  have hscalarPower : scalar ^ (prime ^ exponent) = 1 := by
    have heq := hiterate (prime ^ exponent)
    rw [hpower] at heq
    change basisVector = scalar ^ (prime ^ exponent) • basisVector at heq
    have hsmul : scalar ^ (prime ^ exponent) • basisVector = (1 : field) • basisVector := by
      simpa only [one_smul] using heq.symm
    exact (smul_left_injective field hvectorNe) hsmul
  have hscalarOne := char_prime_power_eq_one prime hprime scalar exponent hscalarPower
  have hfixed : equivalence basisVector = basisVector := by
    rw [hscalarOne, one_smul] at hscalar
    exact hscalar.symm
  apply LinearEquiv.ext
  intro member
  obtain ⟨coefficient, rfl⟩ := hspan member
  rw [map_smul, hfixed]
  rfl

end CFSG.RankThreeEvenClassification.Helpers
