module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem prime_fixed_point_free_coprime {K R : Type*} [Group K] [Finite K] [Group R] [Finite R]
    [MulDistribMulAction R K] {r : ℕ} (hr : r.Prime) (hR : Nat.card R = r)
    (hfix : ∀ k : K, (∀ g : R, g • k = k) → k = 1) : ¬ r ∣ Nat.card K := by
  have : Fact r.Prime := ⟨hr⟩
  have hRp : IsPGroup r R := IsPGroup.of_card (n := 1) (by rw [hR, pow_one])
  intro hdvd
  have h1 : (1 : K) ∈ MulAction.fixedPoints R K := fun g => smul_one g
  obtain ⟨b, hb, hne⟩ := hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point K hdvd h1
  exact hne (hfix b hb).symm

end CFSG.GroupTheory.SteinbergBK
