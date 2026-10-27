module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualEven

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem perfectInLayer_triality_outer_three {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K₃ : Type} [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    PerfectInLayer φ := by
  have hℓ : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  · subst h2
    exact outer_three_even hf hK₃ Fr hFr φ hφ3 hφ
  · have hℓ5 : 5 ≤ ℓ := by
      have := hℓ.two_le
      have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; exact absurd hℓ (by norm_num)
      omega
    have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
      hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    rcases (show (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 by omega) with hq | hq
    · exact outer_three_odd_one hℓ5 hf hq hK₃ Fr hFr φ hφ3 hφ
    · exact outer_three_odd_two hℓ5 hf hq hK₃ Fr hFr φ hφ3 hφ

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
