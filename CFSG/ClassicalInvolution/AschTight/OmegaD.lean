module

public import CFSG.ClassicalInvolution.AschTight.Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem isUniqueInvolution_of_tight (ht : S19R.TightStdDelta p f K z) : IsUniqueInvolution K z := by
  have hU := uniqueInvolutionNormal_of_tight ht
  refine ⟨hU.2.1, ?_, ?_, ?_⟩
  · intro h
    have h2 := hU.1
    rw [h, orderOf_one] at h2
    omega
  · rw [← sq, ← hU.1, pow_orderOf_eq_one]
  · intro y hy hy2
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hU.2.2.1 y hy (orderOf_eq_prime (by rw [sq]; exact hy2) h1))

theorem conjSub_eq_conjSub_of_tight (ht : S19R.TightStdDelta p f K z) {a b : G}
    (h : a * z * a⁻¹ = b * z * b⁻¹) : conjSub a K = conjSub b K := by
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht, Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h]
      _ = z * (b⁻¹ * a) := by group
  calc conjSub a K = conjSub b (conjSub (b⁻¹ * a) K) := by rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b K := by rw [conjSub_eq_of_mem_normalizer hn]

theorem odd_card_inf_of_tight (ht : S19R.TightStdDelta p f K z) {K₁ J : Subgroup G}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass K) (hJ : J ∈ CoreAssembly.conjClass K) (hne : K₁ ≠ J) :
    Odd (Nat.card ↥(K₁ ⊓ J)) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K K₁ hK₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu'
    omega
  have huu : (u : G) * u = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
  have hI := isUniqueInvolution_of_tight ht
  have ha := ((hI.conj a).unique u (Subgroup.mem_inf.mp u.2).1 huu).resolve_left hu1
  have hb := ((hI.conj b).unique u (Subgroup.mem_inf.mp u.2).2 huu).resolve_left hu1
  exact hne (conjSub_eq_conjSub_of_tight ht (ha.symm.trans hb))

theorem padicValNat_card_inf_eq_zero_of_tight (ht : S19R.TightStdDelta p f K z) {K₁ J : Subgroup G}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass K) (hJ : J ∈ CoreAssembly.conjClass K) (hne : K₁ ≠ J) :
    padicValNat 2 (Nat.card ↥(K₁ ⊓ J)) = 0 := by
  refine padicValNat.eq_zero_of_not_dvd fun h2 => ?_
  exact (Nat.not_even_iff_odd.mpr (odd_card_inf_of_tight ht hK₁ hJ hne)) (even_iff_two_dvd.mpr h2)

theorem omega4_of_tight (ht : S19R.TightStdDelta p f K z) :
    ∀ K₁ ∈ CoreAssembly.conjClass K, ∀ J ∈ CoreAssembly.conjClass K, K₁ ≠ J →
      padicValNat 2 (Nat.card ↥(K₁ ⊓ J)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(K₁ ⊓ J)) = 1 → Commutes K₁ J) := by
  intro K₁ hK₁ J hJ hne
  have h0 := padicValNat_card_inf_eq_zero_of_tight ht hK₁ hJ hne
  refine ⟨by omega, fun h1 => ?_⟩
  omega

theorem mem_normalizer_of_commute_of_tight (ht : S19R.TightStdDelta p f K z) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass K) {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁) {v : G}
    (hv : v * z₁ = z₁ * v) : v ∈ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class K K₁ hK₁
  obtain rfl : z₁ = a * z * a⁻¹ := hz₁.eq ((isUniqueInvolution_of_tight ht).conj a)
  have hconj : conjSub v (conjSub a K) = conjSub a K := by
    rw [← conjSub_mul]
    apply conjSub_eq_conjSub_of_tight ht
    calc v * a * z * (v * a)⁻¹ = v * (a * z * a⁻¹) * v⁻¹ := by group
      _ = a * z * a⁻¹ * v * v⁻¹ := by rw [hv]
      _ = a * z * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : v * x * v⁻¹ ∈ conjSub v (conjSub a K) ↔ x ∈ conjSub a K := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  rw [hconj] at hx
  exact hx.symm

theorem omega5_of_tight (ht : S19R.TightStdDelta p f K z) :
    ∀ K₁ ∈ CoreAssembly.conjClass K, ∀ J ∈ CoreAssembly.conjClass K, K₁ ≠ J → ∀ z₁ : G,
      IsUniqueInvolution K₁ z₁ → ∀ v ∈ J, (¬ ∀ w ∈ J, v * w = w * v) →
        IsPGroup 2 (Subgroup.zpowers v) → v * z₁ = z₁ * v →
          v ∈ Subgroup.normalizer (K₁ : Set G) :=
  fun _ hK₁ _ _ _ _ hz₁ _ _ _ _ hv => mem_normalizer_of_commute_of_tight ht hK₁ hz₁ hv

theorem conjInvariant_of_tight [IsSimpleGroup G] (ht : S19R.TightStdDelta p f K z) :
    ConjInvariant (CoreAssembly.conjClass K) :=
  (inClass_conjugates ht.branch.member).conjInvariant

theorem classical_of_tight [IsSimpleGroup G] (ht : S19R.TightStdDelta p f K z) :
    ∀ L ∈ CoreAssembly.conjClass K, ∃ z' : G, IsClassicalMember p f L z' :=
  (inClass_conjugates ht.branch.member).classical

theorem hypOmegaMod_of_tight [IsSimpleGroup G] (ht : S19R.TightStdDelta p f K z) :
    Asc77.HypOmegaMod p f (CoreAssembly.conjClass K) where
  conjInvariant := conjInvariant_of_tight ht
  classical := classical_of_tight ht
  omega4 K₁ hK₁ J hJ hne := by
    have h0 := padicValNat_card_inf_eq_zero_of_tight ht hK₁ hJ hne
    refine ⟨by omega, fun h1 => ?_⟩
    exfalso
    omega
  omega5 := omega5_of_tight ht

theorem hypOmegaMod_of_tightD [IsSimpleGroup G] (ht : S19R.TightStd p f K z) :
    Asc77.HypOmegaMod p f (CoreAssembly.conjClass K) :=
  hypOmegaMod_of_tight ht.toTightBranch

end CFSG.ClassicalInvolution.Disconnected.AschTight
