module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513SL

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private lemma sec5b513_zeta_sq {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz2 : z * z = 1) : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
  rw [← map_mul, ← map_one e]
  congr 1
  apply Subtype.ext
  simpa using hz2

private lemma sec5b513_zeta_ne_one {K : Subgroup G} (e : ↥K ≃* SL23) {z : G} (hz : z ∈ K)
    (hz1 : z ≠ 1) : e ⟨z, hz⟩ ≠ 1 := by
  intro hc
  have hsub : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
  exact hz1 (congrArg Subtype.val hsub)

private lemma sec5b513_map_pow4_eq_one {K : Subgroup G} (e : ↥K ≃* SL23) {u : G} (hu : u ∈ K) :
    (e ⟨u, hu⟩) ^ 4 = 1 ↔ u ^ 4 = 1 := by
  constructor
  · intro h
    have hsub : (⟨u, hu⟩ : ↥K) ^ 4 = 1 := e.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val hsub
  · intro h
    rw [← map_pow, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using h

theorem sec5b513_conj_of_sq {K : Subgroup G} (e : ↥K ≃* SL23) {z a b : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (ha : a ∈ K) (hb : b ∈ K) (ha2 : a * a = z)
    (hb2 : b * b = z) : ∃ u ∈ K, u⁻¹ * a * u = b := by
  have hA : e ⟨a, ha⟩ * e ⟨a, ha⟩ = e ⟨z, hz⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simpa using ha2
  have hB : e ⟨b, hb⟩ * e ⟨b, hb⟩ = e ⟨z, hz⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simpa using hb2
  obtain ⟨v, hv⟩ := sec5b513_sl23_conj_of_sq (sec5b513_zeta_sq e hz hz2)
    (sec5b513_zeta_ne_one e hz hz1) hA hB
  refine ⟨(e.symm v : ↥K), (e.symm v).2, ?_⟩
  have h1 : e.symm v ⁻¹ * (⟨a, ha⟩ : ↥K) * e.symm v = ⟨b, hb⟩ := by
    apply e.injective
    simp only [map_mul, map_inv, e.apply_symm_apply, hv]
  simpa using congrArg Subtype.val h1

theorem sec5b513_anti {K : Subgroup G} (e : ↥K ≃* SL23) {z a u : G} (hz : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (ha : a ∈ K) (hu : u ∈ K) (ha2 : a * a = z)
    (hu4 : u ^ 4 ≠ 1) : a * (u⁻¹ * a * u) = z * ((u⁻¹ * a * u) * a) := by
  have hA : e ⟨a, ha⟩ * e ⟨a, ha⟩ = e ⟨z, hz⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simpa using ha2
  have hU4 : (e ⟨u, hu⟩) ^ 4 ≠ 1 := fun h => hu4 ((sec5b513_map_pow4_eq_one e hu).1 h)
  have h1 : (⟨a, ha⟩ : ↥K) * ((⟨u, hu⟩ : ↥K)⁻¹ * ⟨a, ha⟩ * ⟨u, hu⟩) =
      (⟨z, hz⟩ : ↥K) * (((⟨u, hu⟩ : ↥K)⁻¹ * ⟨a, ha⟩ * ⟨u, hu⟩) * ⟨a, ha⟩) := by
    apply e.injective
    simp only [map_mul, map_inv]
    exact (sec5b513_sl23_comm_or_anti (sec5b513_zeta_sq e hz hz2)
      (sec5b513_zeta_ne_one e hz hz1) hA).2 hU4
  simpa using congrArg Subtype.val h1

theorem sec5b513_split {K : Subgroup G} (e : ↥K ≃* SL23) {g : G} (hg : g ∈ K) :
    ∃ u ∈ K, u ^ 4 ≠ 1 ∧ (u⁻¹ * g) ^ 4 ≠ 1 := by
  obtain ⟨v, hv1, hv2⟩ := sec5b513_sl23_split (e ⟨g, hg⟩)
  refine ⟨(e.symm v : ↥K), (e.symm v).2, ?_, ?_⟩
  · intro hc
    apply hv1
    have h1 : (e ⟨(e.symm v : G), (e.symm v).2⟩) ^ 4 = 1 :=
      (sec5b513_map_pow4_eq_one e (e.symm v).2).mpr hc
    rwa [e.apply_symm_apply v] at h1
  · intro hc
    apply hv2
    have hem : e (e.symm v) = v := e.apply_symm_apply v
    have hx : e ((e.symm v)⁻¹ * (⟨g, hg⟩ : ↥K)) = v⁻¹ * e ⟨g, hg⟩ := by
      rw [map_mul, map_inv, hem]
    have hsub : ((e.symm v)⁻¹ * (⟨g, hg⟩ : ↥K)) ^ 4 = 1 := by
      apply Subtype.ext
      simpa using hc
    have hpow : (e ((e.symm v)⁻¹ * (⟨g, hg⟩ : ↥K))) ^ 4 = 1 := by
      rw [← map_pow, hsub, map_one]
    rwa [hx] at hpow

end CFSG.OddStandard.SmallF3.Omega
