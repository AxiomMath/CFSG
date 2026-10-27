module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module

theorem exists_not_mem_span_singleton {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : 2 ≤ finrank K V) {v : V} (hv : v ≠ 0) : ∃ w : V, w ∉ K ∙ v := by
  by_contra h
  simp only [not_exists, not_not] at h
  have htop : K ∙ v = ⊤ := eq_top_iff.2 fun w _ => h w
  have h1 := finrank_span_singleton (K := K) hv
  rw [htop, finrank_top] at h1
  omega

theorem finite_anisotropic_plane_regular {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] (hV : 2 ≤ finrank K V) {Q : QuadraticForm K V} (hQ : ∀ x, x ≠ 0 → Q x ≠ 0) :
    (polarBilin Q).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  by_contra hv0
  by_cases h2 : (2 : K) = 0
  ·
    have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    obtain ⟨w, hw⟩ := exists_not_mem_span_singleton hV hv0
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q v)
    obtain ⟨t, ht⟩ := isSquare_of_charTwo' (Q w)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hQ v hv0 (by rw [hs, mul_zero])
    have hx0 : t • v + s • w ≠ 0 := by
      intro h
      apply hw
      have h' : s • w = -(t • v) := eq_neg_of_add_eq_zero_right h
      have hwv : w = (-(s⁻¹ * t)) • v := by
        calc w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
          _ = (-(s⁻¹ * t)) • v := by rw [h', smul_neg, smul_smul, neg_smul]
      rw [hwv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    apply hQ _ hx0
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hv w, smul_zero, smul_zero, add_zero, hs, ht, smul_eq_mul, smul_eq_mul]
    linear_combination (t * t * (s * s)) * h2
  ·
    have h := hv v
    rw [polar_self_eq_two_mul] at h
    exact hQ v hv0 ((mul_eq_zero.1 h).resolve_left h2)

end CFSG.LocalAnalysis.ComponentInitial
