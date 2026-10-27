module

public import CFSG.ClassicalGroups.Orthogonal.InvariantPairing

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

private theorem exists_perp_anisotropic_vector {ι : Type} [Fintype ι] {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) {u : ι → K} (hu0 : u ≠ 0) :
    ∃ w : ι → K, polar Q' u w = 0 ∧ Q' w ≠ 0 := by
  obtain ⟨s, w₀, hs, hw₀, hsw⟩ := exists_perp_pair_polar_ne_zero hQ h3 hu0
  by_cases hs0 : Q' s = 0
  · by_cases hw0 : Q' w₀ = 0
    · refine ⟨s + w₀, by rw [polar_add_right, hs, hw₀, add_zero], fun h => hsw ?_⟩
      have h1 := QuadraticMap.map_add Q' s w₀
      rw [h, hs0, hw0] at h1
      simpa using h1.symm
    · exact ⟨w₀, hw₀, hw0⟩
  · exact ⟨s, hs, hs0⟩

theorem exists_perp_map_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [CharP K 2] {Q' : QuadraticForm K (ι → K)}
    (hQ : (QuadraticMap.polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K))
    {u : ι → K} (hu0 : u ≠ 0) (κ : K) :
    ∃ v : ι → K, QuadraticMap.polar Q' u v = 0 ∧ Q' v = κ := by
  obtain ⟨w, hw, hQw⟩ := exists_perp_anisotropic_vector hQ h3 hu0
  obtain ⟨c, hc⟩ : ∃ c : K, c ^ 2 = κ / Q' w := by
    refine ⟨(frobeniusEquiv K 2).symm (κ / Q' w), ?_⟩
    have h := (frobeniusEquiv K 2).apply_symm_apply (κ / Q' w)
    rwa [frobeniusEquiv_def] at h
  refine ⟨c • w, by rw [polar_smul_right, hw, smul_zero], ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← _root_.sq, hc, div_mul_cancel₀ κ hQw]

end CFSG.ClassicalGroups.Orthogonal

end
