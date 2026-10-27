module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSuzuki

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Lang.Coordinator

theorem not_three_dvd_suzuki_numerator {f₀ : ℕ} (hf₀ : Odd f₀) :
    ¬ 3 ∣ lieOrderNumerator .twistedB2 0 (2 ^ f₀) := by
  obtain ⟨m, rfl⟩ := hf₀
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    simp
  have hq : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [hq]
  generalize 4 ^ m = u at h4
  have hu : 1 ≤ u := by omega
  intro h3
  simp only [lieOrderNumerator] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · have h' : (2 * u) ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod]
        have : (2 * u) % 3 = 2 := by omega
        rw [this]
      omega
  · omega

theorem noL2OuterAt_sz : NoL2OuterAt FamSz := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hninn
  obtain rfl := hF
  have hdiv : ¬ 3 ∣ lieOrderDivisor .twistedB2 n (p ^ f) := by
    simp [lieOrderDivisor]
  have hb := outerFixedOrderBoundAt_twistedB2 P n p f hadm hm ht 3 Nat.prime_three (by norm_num)
    hdiv (by simp) ψ hψ3 hninn
  rcases hb with ⟨f₀, hf, hdvd⟩ | ⟨h, -⟩
  · obtain ⟨hp, hf1, hn0, hp2, hfodd, hf3⟩ := hadm
    subst hn0
    subst hp2
    have hf₀ : Odd f₀ := by
      rw [hf] at hfodd
      exact (Nat.odd_mul.1 hfodd).2
    apply noL2_of_not_three_dvd_fixed
    intro h3
    have hfix : fixSubgroup ψ = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup ψ :=
      Subgroup.ext fun x => Iff.rfl
    rw [hfix] at h3
    exact not_three_dvd_suzuki_numerator hf₀ (h3.trans hdvd)
  · exact absurd h (by decide)

theorem y923_lieRestAt_sz : Y923_LieRestAt FamSz :=
  y923_lieRestAt_of_noL2Outer noL2OuterAt_sz

end CFSG.HardMathSupport.Dickson.Sec6.I923
