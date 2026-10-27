module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthCentGen
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSixOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank

theorem aut_inner_plus {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hfpf : HasFixedPointFreeOrder true n p) :
    ∀ σ : MulAut ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))), σ ^ p = 1 →
      ∃ y, σ = MulAut.conj y := by
  have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfpf
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · simp only [typeSign, ite_true] at hdvd
      have : p ∣ 1 := by simpa using hdvd
      exact absurd (Nat.dvd_one.1 this) hp.ne_one
    · exact statedOmega_quadPlus_three_aut_odd_inner hp hp2
  · refine statedOmega_quadPlus_aut_odd_inner (n + 1) p (by omega) hp hp2 ?_
    rintro ⟨rfl, hn4⟩
    have hn3 : n = 3 := by omega
    subst hn3
    simp only [typeSign, ite_true] at hdvd
    omega

theorem aut_inner_minus (hU : AutU42Five) {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hfpf : HasFixedPointFreeOrder false n p) :
    ∀ σ : MulAut ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)), σ ^ p = 1 →
      ∃ y, σ = MulAut.conj y := by
  have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfpf
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · exact statedOmega_quadMinus_two_aut_odd_inner hp hp2
    · simp only [typeSign, Bool.false_eq_true, ite_false] at hdvd
      have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hdvd)
      subst hp5
      exact fun σ hσ => hU σ hσ
  · exact statedOmega_quadMinus_aut_odd_inner (n + 1) p (by omega) hp hp2

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
