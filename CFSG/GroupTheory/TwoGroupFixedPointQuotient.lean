module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

theorem exists_fixed_coset_of_isPGroup_two {K : Type} [Group K] [Finite K]
    {A R T : Subgroup K} (hA2 : IsPGroup 2 A) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set K))
    (hAT : A ≤ Subgroup.normalizer (T : Set K))
    (hTR : T ≤ R) (hlt : T < R) :
    ∃ r : K, r ∈ R ∧ r ∉ T ∧ ∀ a ∈ A, a * r * a⁻¹ * r⁻¹ ∈ T := by
  classical
  letI : MulAction A R := MulAction.compHom R (Subgroup.inclusion hAR)
  have hsmul_coe : ∀ (a : A) (x : R),
      ((a • x : R) : K) = (a : K) * (x : K) * (a : K)⁻¹ :=
    fun _ _ => rfl
  have hquotAction : MulAction.QuotientAction A (T.subgroupOf R) :=
    ⟨fun a r r' hmem => by
      rw [Subgroup.mem_subgroupOf] at hmem ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem ⊢
      rw [hsmul_coe a r, hsmul_coe a r']
      have hh : (a : K) * ((r : K)⁻¹ * (r' : K)) * (a : K)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hAT a.2) ((r : K)⁻¹ * (r' : K))).mp hmem
      convert hh using 1 <;> group⟩
  letI : MulAction.QuotientAction A (T.subgroupOf R) := hquotAction
  have h1 : (QuotientGroup.mk (1 : R) : R ⧸ T.subgroupOf R) ∈
      MulAction.fixedPoints A (R ⧸ T.subgroupOf R) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hsmul_coe a 1]
    simp
  have hdvd : 2 ∣ Nat.card (R ⧸ T.subgroupOf R) := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf R)
    have hTcard : Nat.card (T.subgroupOf R) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
    have hq_dvd : Nat.card (R ⧸ T.subgroupOf R) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.card_quotient_dvd_card (T.subgroupOf R)
    have hq_ne_one : Nat.card (R ⧸ T.subgroupOf R) ≠ 1 := by
      intro hq
      have hlt' : Nat.card (T.subgroupOf R) < Nat.card (T.subgroupOf R) := by
        calc
          Nat.card (T.subgroupOf R) = Nat.card T := hTcard
          _ < Nat.card R := Subgroup.card_lt_of_lt hlt
          _ = Nat.card (R ⧸ T.subgroupOf R) * Nat.card (T.subgroupOf R) := hcard
          _ = Nat.card (T.subgroupOf R) := by rw [hq, one_mul]
      exact lt_irrefl _ hlt'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hq_dvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hq_ne_one hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨q, hqfix, hqne⟩ :=
    hA2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := R ⧸ T.subgroupOf R) hdvd h1
  obtain ⟨r₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ a : A, a • (QuotientGroup.mk r₀ : R ⧸ T.subgroupOf R) =
      QuotientGroup.mk r₀ := fun a => MulAction.mem_fixedPoints.mp hqfix a
  have hr₀ : r₀ ∉ T.subgroupOf R := by
    intro hmem
    apply hqne
    rw [QuotientGroup.eq]
    simpa using hmem
  refine ⟨(r₀ : K)⁻¹, R.inv_mem r₀.2, ?_, ?_⟩
  · intro h
    exact hr₀ ((Subgroup.mem_subgroupOf).mpr (by simpa using T.inv_mem h))
  · intro a ha
    have hcomm : a * (r₀ : K)⁻¹ * a⁻¹ * ((r₀ : K)⁻¹)⁻¹ ∈ T := by
      have hmem : ((⟨a, ha⟩ : A) • r₀)⁻¹ * r₀ ∈ T.subgroupOf R := by
        have h := hfix ⟨a, ha⟩
        rw [MulAction.Quotient.smul_mk] at h
        exact (QuotientGroup.eq).mp h
      rw [Subgroup.mem_subgroupOf] at hmem
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
      rw [hsmul_coe ⟨a, ha⟩ r₀] at hmem
      simpa [mul_inv_rev, mul_assoc] using hmem
    simpa using hcomm

end CFSG
