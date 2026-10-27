module

public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed

universe u

variable {G : Type u} [Group G]

theorem zpowers_eq_of_prime_card [Finite G] {P : Subgroup G} (hP : (Nat.card P).Prime) {u : G}
    (hu : u ∈ P) (hu1 : u ≠ 1) : Subgroup.zpowers u = P := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu)
  rw [Nat.card_zpowers]
  rcases (Nat.dvd_prime hP).mp (Subgroup.orderOf_dvd_natCard P hu) with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hu1
  · exact h2.ge

theorem mem_normalizer_of_conj_mem [Finite G] {P : Subgroup G} (hP : (Nat.card P).Prime)
    {g u : G} (hu : u ∈ P) (hu1 : u ≠ 1) (hgu : g * u * g⁻¹ ∈ P) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  have hzp := zpowers_eq_of_prime_card hP hu hu1
  have hgu1 : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  have hzp' := zpowers_eq_of_prime_card hP hgu hgu1
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hzp] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact P.zpow_mem hgu k
  · intro hgh
    rw [← hzp'] at hgh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgh
    rw [conj_zpow] at hk
    have hk' : u ^ k = h := by
      have := congrArg (fun x => g⁻¹ * x * g) hk
      simpa [mul_assoc] using this
    rw [← hk']
    exact P.zpow_mem hu k

theorem card_filter_mem_ne_one [Fintype G] (P : Subgroup G) :
    (Finset.univ.filter (fun u : G => u ∈ P ∧ u ≠ 1)).card = Nat.card P - 1 := by
  have h1 : Finset.univ.filter (fun u : G => u ∈ P ∧ u ≠ 1) =
      (Finset.univ.filter (fun u : G => u ∈ P)).erase 1 := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [h1, Finset.card_erase_of_mem (by simp [P.one_mem]), ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]

theorem sum_conjugatorCount_prime_subgroup [Fintype G] {P : Subgroup G}
    (hP : (Nat.card P).Prime) :
    ∑ u ∈ Finset.univ.filter (fun u => u ∈ P ∧ u ≠ 1),
        ∑ v ∈ Finset.univ.filter (fun v => v ∈ P ∧ v ≠ 1), conjugatorCount u v =
      ((Nat.card P - 1 : ℕ) : ℂ) * Nat.card (Subgroup.normalizer (P : Set G)) := by
  classical
  set U : Finset G := Finset.univ.filter (fun u => u ∈ P ∧ u ≠ 1) with hU
  have hcardU : U.card = Nat.card P - 1 := by rw [hU, card_filter_mem_ne_one]
  unfold conjugatorCount
  have hswap : ∑ u ∈ U, ∑ v ∈ U, ∑ g : G, (if g * u * g⁻¹ = v then (1 : ℂ) else 0) =
      ∑ g : G, ∑ u ∈ U, (if g * u * g⁻¹ ∈ U then (1 : ℂ) else 0) := by
    have h1 : ∀ u ∈ U, ∑ v ∈ U, ∑ g : G, (if g * u * g⁻¹ = v then (1 : ℂ) else 0) =
        ∑ g : G, (if g * u * g⁻¹ ∈ U then (1 : ℂ) else 0) := by
      intro u _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  rw [hswap]
  have hinner : ∀ g : G, ∑ u ∈ U, (if g * u * g⁻¹ ∈ U then (1 : ℂ) else 0) =
      if g ∈ Subgroup.normalizer (P : Set G) then ((Nat.card P - 1 : ℕ) : ℂ) else 0 := by
    intro g
    by_cases hg : g ∈ Subgroup.normalizer (P : Set G)
    · rw [ite_eq_left hg, ← hcardU, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_congr rfl fun u hu => ?_
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [ite_eq_left]
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg u).mp hu.1, fun h => hu.2 ?_⟩
      have := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using this
    · rw [ite_eq_right hg]
      refine Finset.sum_eq_zero fun u hu => ?_
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [ite_eq_right]
      intro hgu
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hgu
      exact hg (mem_normalizer_of_conj_mem hP hu.1 hu.2 hgu.1)
  simp_rw [hinner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem selfcentralizing_prime_subgroup_column_average_constant_row_bound [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {p : ℕ} (hp : p.Prime) (P : Subgroup G)
    (_hPcyc : IsCyclic P) (hP : Nat.card P = p)
    (_hcent : Subgroup.centralizer (P : Set G) = P) {e : ℕ}
    (he : e = P.relIndex (Subgroup.normalizer (P : Set G))) (Λ : Finset basis.index)
    (c : basis.index → ℂ)
    (hc : ∀ χ ∈ Λ, ∀ u ∈ P, u ≠ 1 → (basis.representation χ).character u = c χ) :
    (∑ χ ∈ Λ, ‖c χ‖ ^ 2 ≤ (p * e : ℝ) / (p - 1)) ∧
    ((∀ χ ∈ Λ, ‖c χ‖ = 1) → (Λ.card : ℝ) ≤ (p * e : ℝ) / (p - 1)) ∧
    ((∀ χ ∈ Λ, ‖c χ‖ = 1) → e < p - 1 → Λ.card ≤ e) := by
  have hPp : (Nat.card P).Prime := hP ▸ hp
  have hp2 : 2 ≤ p := hp.two_le
  set U : Finset G := Finset.univ.filter (fun u => u ∈ P ∧ u ≠ 1) with hU
  have hcardU : U.card = p - 1 := by rw [hU, card_filter_mem_ne_one, hP]
  have hN : (Nat.card (Subgroup.normalizer (P : Set G)) : ℝ) = p * e := by
    have h := Subgroup.relIndex_mul_card P (Subgroup.normalizer (P : Set G))
    rw [inf_of_le_left Subgroup.le_normalizer, hP, ← he] at h
    rw [← h]
    push_cast
    ring
  set S : basis.index → ℂ := fun χ => ∑ u ∈ U, (basis.representation χ).character u with hS
  have hcol : ∑ χ, ((‖S χ‖ ^ 2 : ℝ) : ℂ) = ∑ u ∈ U, ∑ v ∈ U, conjugatorCount u v := by
    simp_rw [← complete_complex_character_column_sum basis]
    have hterm : ∀ χ, ((‖S χ‖ ^ 2 : ℝ) : ℂ) = ∑ u ∈ U, ∑ v ∈ U,
        (basis.representation χ).character v *
          starRingEnd ℂ ((basis.representation χ).character u) := by
      intro χ
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hS, map_sum, Finset.sum_mul_sum,
        Finset.sum_comm]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  have hreal : ∑ χ, ‖S χ‖ ^ 2 = ((p : ℝ) - 1) * (p * e) := by
    have h := hcol.trans (sum_conjugatorCount_prime_subgroup hPp)
    rw [hP] at h
    have h' : ((∑ χ, ‖S χ‖ ^ 2 : ℝ) : ℂ) =
        ((((p - 1 : ℕ) : ℝ) * (Nat.card (Subgroup.normalizer (P : Set G)) : ℝ) : ℝ) : ℂ) := by
      push_cast at h ⊢
      exact h
    rw [Complex.ofReal_injective h', hN, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hSΛ : ∀ χ ∈ Λ, ‖S χ‖ ^ 2 = ((p : ℝ) - 1) ^ 2 * ‖c χ‖ ^ 2 := by
    intro χ hχ
    have hsum : S χ = ((p - 1 : ℕ) : ℂ) * c χ := by
      simp only [hS]
      rw [Finset.sum_congr rfl fun u hu => hc χ hχ u
          (Finset.mem_filter.mp hu).2.1 (Finset.mem_filter.mp hu).2.2,
        Finset.sum_const, hcardU, nsmul_eq_mul]
    rw [hsum, norm_mul, Complex.norm_natCast, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one,
      mul_pow]
  have hmain : ((p : ℝ) - 1) ^ 2 * ∑ χ ∈ Λ, ‖c χ‖ ^ 2 ≤ ((p : ℝ) - 1) * (p * e) := by
    rw [← hreal, Finset.mul_sum]
    calc ∑ χ ∈ Λ, ((p : ℝ) - 1) ^ 2 * ‖c χ‖ ^ 2 = ∑ χ ∈ Λ, ‖S χ‖ ^ 2 :=
          Finset.sum_congr rfl fun χ hχ => (hSΛ χ hχ).symm
      _ ≤ ∑ χ, ‖S χ‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun χ _ _ => by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hbound : ∑ χ ∈ Λ, ‖c χ‖ ^ 2 ≤ (p * e : ℝ) / (p - 1) := by
    rw [le_div_iff₀ hp1]
    nlinarith [hmain]
  have hcard : (∀ χ ∈ Λ, ‖c χ‖ = 1) → (Λ.card : ℝ) ≤ (p * e : ℝ) / (p - 1) := by
    intro h1
    have : ∑ χ ∈ Λ, ‖c χ‖ ^ 2 = Λ.card := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [h1 χ hχ, one_pow], Finset.sum_const,
        nsmul_eq_mul, mul_one]
    rw [← this]
    exact hbound
  refine ⟨hbound, hcard, fun h1 hep => ?_⟩
  have h := hcard h1
  rw [le_div_iff₀ hp1] at h
  have hep' : (e : ℝ) + 1 < p := by
    have : e + 1 < p := by omega
    exact_mod_cast this
  have hlt : (Λ.card : ℝ) < e + 1 := by
    by_contra hge
    push Not at hge
    nlinarith
  have : Λ.card < e + 1 := by exact_mod_cast hlt
  omega

end CFSG.Semidihedral.Principal
