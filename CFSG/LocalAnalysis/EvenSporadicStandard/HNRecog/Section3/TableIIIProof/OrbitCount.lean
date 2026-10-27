module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

private def t3_orbit (K : Subgroup G) (c : G) : Set G :=
  {x : G | ∃ k ∈ K, k * c * k⁻¹ = x}

private lemma t3_isConjOrbit (K : Subgroup G) (c : G) :
    IsConjOrbit K (t3_orbit K c) where
  conj_mem := by
    rintro k' hk' x ⟨k, hk, rfl⟩
    refine ⟨k' * k, K.mul_mem hk' hk, ?_⟩
    rw [mul_inv_rev]
    group
  nonempty := ⟨c, 1, K.one_mem, by simp⟩
  transitive := by
    rintro x ⟨k₁, hk₁, rfl⟩ y ⟨k₂, hk₂, rfl⟩
    refine ⟨k₂ * k₁⁻¹, K.mul_mem hk₂ (K.inv_mem hk₁), ?_⟩
    rw [mul_inv_rev]
    group

theorem tableIII_card_le_of_conj_mem [Finite G] {K : Subgroup G} {T : Set G}
    (hT : ∀ k ∈ K, ∀ c ∈ T, k * c * k⁻¹ ∈ T) {c : G} (hc : c ∈ T) :
    Nat.card K ≤ Nat.card ↥T * Nat.card ↥(K ⊓ Gx c) := by
  classical
  have hO := t3_isConjOrbit K c
  have hcO : c ∈ t3_orbit K c := ⟨1, K.one_mem, by simp⟩
  have hstab := hO.card_mul_card_stab hcO
  have hsub : t3_orbit K c ⊆ T := by
    rintro x ⟨k, hk, rfl⟩
    exact hT k hk c hc
  have hcard : Nat.card ↥(t3_orbit K c) ≤ Nat.card ↥T := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub
  rw [← hstab]
  exact Nat.mul_le_mul_right _ hcard

theorem tableIII_dvd_card_of_conj_mem [Finite G] {K : Subgroup G} {T : Set G} {d : ℕ}
    (hT : ∀ k ∈ K, ∀ c ∈ T, k * c * k⁻¹ ∈ T)
    (hd : ∀ c ∈ T, d * Nat.card ↥(K ⊓ Gx c) ∣ Nat.card K) : d ∣ Nat.card ↥T := by
  classical
  let P : ℕ → Prop := fun n => ∀ (T : Set G) (d : ℕ), T.ncard = n →
      (∀ k ∈ K, ∀ c ∈ T, k * c * k⁻¹ ∈ T) →
      (∀ c ∈ T, d * Nat.card ↥(K ⊓ Gx c) ∣ Nat.card K) → d ∣ T.ncard
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih T d hn hT hd
    by_cases hne : T.Nonempty
    · obtain ⟨c, hc⟩ := hne
      let O := t3_orbit K c
      let T' := T \ O
      have hO := t3_isConjOrbit K c
      have hcO : c ∈ O := ⟨1, K.one_mem, by simp⟩
      have hstab := hO.card_mul_card_stab hcO
      have hsub : O ⊆ T := by
        rintro x ⟨k, hk, rfl⟩
        exact hT k hk c hc
      have hs : 0 < Nat.card ↥(K ⊓ Gx c) := by
        haveI : Nonempty ↥(K ⊓ Gx c) := ⟨⟨1, ⟨K.one_mem, mem_Gx.mpr (by simp)⟩⟩⟩
        exact Nat.card_pos
      have hdvdO : d ∣ Nat.card ↥O := by
        have h := hd c hc
        rw [← hstab] at h
        exact Nat.dvd_of_mul_dvd_mul_right hs h
      have hT' : ∀ k ∈ K, ∀ x ∈ T', k * x * k⁻¹ ∈ T' := by
        rintro k hk x ⟨hxT, hxO⟩
        refine ⟨hT k hk x hxT, ?_⟩
        intro hmem
        have hmem' : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ ∈ O :=
          hO.conj_mem k⁻¹ (K.inv_mem hk) _ hmem
        rw [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x by group] at hmem'
        exact hxO hmem'
      have hdT' : ∀ y ∈ T', d * Nat.card ↥(K ⊓ Gx y) ∣ Nat.card K :=
        fun y hy => hd y hy.1
      have hdecomp : T'.ncard + O.ncard = T.ncard := Set.ncard_sdiff_add_ncard_of_subset hsub
      have hOpos : 0 < O.ncard := by
        rw [Set.ncard_pos]
        exact ⟨c, hcO⟩
      have hlt : T'.ncard < n := by
        rw [← hn]
        omega
      have hdvdT' : d ∣ T'.ncard := ih T'.ncard hlt T' d rfl hT' hdT'
      have hdvdT : d ∣ T.ncard := by
        rw [← hdecomp]
        exact Nat.dvd_add hdvdT' hdvdO
      exact hdvdT
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
      exact dvd_zero d
  simpa using hP T.ncard T d rfl hT hd

theorem tableIII_isConjOrbit_of_card_le [Finite G] {K : Subgroup G} {T : Set G}
    (hT : ∀ k ∈ K, ∀ c ∈ T, k * c * k⁻¹ ∈ T) {c : G} (hc : c ∈ T)
    (hle : Nat.card ↥T * Nat.card ↥(K ⊓ Gx c) ≤ Nat.card K) :
    IsConjOrbit K T ∧ Nat.card ↥T * Nat.card ↥(K ⊓ Gx c) = Nat.card K := by
  classical
  have hO := t3_isConjOrbit K c
  have hcO : c ∈ t3_orbit K c := ⟨1, K.one_mem, by simp⟩
  have hstab := hO.card_mul_card_stab hcO
  have hsub : t3_orbit K c ⊆ T := by
    rintro x ⟨k, hk, rfl⟩
    exact hT k hk c hc
  have hs : 0 < Nat.card ↥(K ⊓ Gx c) := by
    haveI : Nonempty ↥(K ⊓ Gx c) := ⟨⟨1, ⟨K.one_mem, mem_Gx.mpr (by simp)⟩⟩⟩
    exact Nat.card_pos
  have hcard : Nat.card ↥T ≤ Nat.card ↥(t3_orbit K c) := by
    have h1 : Nat.card ↥T * Nat.card ↥(K ⊓ Gx c) ≤
        Nat.card ↥(t3_orbit K c) * Nat.card ↥(K ⊓ Gx c) := by
      rw [hstab]
      exact hle
    exact Nat.le_of_mul_le_mul_right h1 hs
  have hEq : t3_orbit K c = T := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    simpa using hcard
  refine ⟨hEq ▸ hO, ?_⟩
  rw [← hEq]
  exact hstab

end CFSG.EvenSporadicStandard.HNRecog.Section3
