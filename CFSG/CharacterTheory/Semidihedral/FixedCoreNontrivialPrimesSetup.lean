module

public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactor
public import CFSG.CharacterTheory.Semidihedral.Principal.ConfinedInvertedOddSubgroup

public section

open scoped Classical

namespace CFSG.Semidihedral.FixedCoreNontrivialPrimes

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryConfinement

theorem three_dvd_mul_sub_one_mul_add_one {q : ℕ} (hq : 1 ≤ q) :
    3 ∣ q * (q - 1) * (q + 1) := by
  have h : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (by omega) _) _
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by omega) _) _
  · exact Dvd.dvd.mul_left (by omega) _

theorem sq_sub_one_eq_mul {q : ℕ} : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [show (1 + m) ^ 2 - 1 = m * (m + 2) by ring_nf; omega,
      show 1 + m - 1 = m by omega]
    ring

theorem trivial_fixed_core_sylow_setup
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ Nat.card (N t))
    (hℓq : ¬ ℓ ∣ p ^ f * (p ^ f - 1) * (p ^ f + 1)) :
    let Y := ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)
    5 ≤ ℓ ∧ ∃ Q : Sylow ℓ (C t),
      ((Q : Subgroup (C t)).map (C t).subtype ≤ (N t).map (C t).subtype) ∧
      (Q : Subgroup (C t)).Normal ∧
      (∀ x ∈ (Q : Subgroup (C t)), ∀ y ∈ (Q : Subgroup (C t)), x * y = y * x) ∧
      Subgroup.centralizer (Q : Set (C t)) = Y ∧
      (∀ x ∈ (Q : Subgroup (C t)), (fS (s n) : G) * x * (fS (s n) : G)⁻¹ = (x : G)⁻¹) ∧
      (∃ Q' : Sylow ℓ G, (Q' : Subgroup G) = (Q : Subgroup (C t)).map (C t).subtype) ∧
      (∀ u ∈ (Q : Subgroup (C t)), u ≠ 1 →
        Subgroup.normalizer (Subgroup.zpowers (u : G) : Set G) ≤ C t) ∧
      Subgroup.normalizer (((Q : Subgroup (C t)).map (C t).subtype : Subgroup G) : Set G) =
        C t ∧
      Subgroup.centralizer (((Q : Subgroup (C t)).map (C t).subtype : Subgroup G) : Set G) =
        Y.map (C t).subtype := by
  intro Y
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set s₀ : G := (fS (s n) : G) with hs₀
  set Na : Subgroup G := (N t).map (C t).subtype with hNa
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hq5 : 5 < p ^ f := by omega
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := by omega
  have hNodd : Odd (Nat.card (N t)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hℓodd : Odd ℓ := hNodd.of_dvd_nat hℓN
  have hℓ5 : 5 ≤ ℓ := by
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl
      exact hℓq (three_dvd_mul_sub_one_mul_add_one hq1)
    have h2 := hℓ.two_le
    have hℓ4 : ℓ ≠ 4 := by
      rintro rfl
      exact absurd hℓ (by norm_num)
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact absurd hℓodd (by decide)
    omega
  refine ⟨hℓ5, ?_⟩
  obtain ⟨U, -, hU, -, -, hUab, -, -, -, hUA, -⟩ :=
    stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action
      G hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC hst.symm hnonab hcentral hnc p f hp hpodd
      hf hq5 hmodel hcov
  have hUNa : U = Na := by
    have h := hUA
    rw [hA₀, sup_bot_eq] at h
    exact h
  have hNainv : ∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ := fun x hx => ((hU x).mp (hUNa ▸ hx)).2
  have hNacomm : ∀ x ∈ Na, ∀ y ∈ Na, x * y = y * x := by
    intro x hx y hy
    rw [← hUNa] at hx hy
    exact congrArg Subtype.val (hUab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hNcomm : ∀ x ∈ N t, ∀ y ∈ N t, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hNacomm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  obtain ⟨hnorm3, hcent3, hTI, -⟩ :=
    stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
      G hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC hst.symm hnonab hcentral hnc p f hp hpodd
      hf hq5 hmodel hcov
  obtain ⟨-, -, -, -, hJN, hYJN, -⟩ :=
    (Local.all_local_prime_centralizer_covers_produce_actual_centralizing_perfect_lift n hn S fS
      hG t ht2 hnonab hcentral hnc p f hp hpodd hf hq5.le hmodel).1
      (EscapingLocalEigensubgroups.all_stationary_covers_give_original_layer_coverage t s₀ hcov)
  have hYcent : Y ≤ Subgroup.centralizer (N t : Set (C t)) := by
    change ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t) ≤ _
    rw [hYJN]
    refine sup_le ?_ ?_
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJN
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hNcomm y hy x hx
  obtain ⟨F₁, hF₁, hF₁fin, A₁, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hT₀ : Nat.card ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) =
      q * (q ^ 2 - 1) := by
    rw [Nat.card_congr eta.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, data.field_card]
  have hT₀index : ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).index = 2 := by
    have h := Subgroup.index_comap_of_surjective
      (H := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
      (QuotientGroup.mk'_surjective (N t))
    exact h.symm.trans hY
  have hNindex : (N t).index = 2 * (q * (q ^ 2 - 1)) := by
    have h := Subgroup.card_mul_index ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    rw [hT₀, hT₀index] at h
    change Nat.card (C t ⧸ N t) = _
    change q * (q ^ 2 - 1) * 2 = Nat.card (H t) at h
    rw [← h]
    ring
  have hℓNindex : ¬ ℓ ∣ (N t).index := by
    rw [hNindex, sq_sub_one_eq_mul]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · apply hℓq
      rw [show q * ((q - 1) * (q + 1)) = q * (q - 1) * (q + 1) by ring] at h2
      exact h2
  obtain ⟨P₀⟩ : Nonempty (Sylow ℓ (N t)) := inferInstance
  set Q₀ : Subgroup (C t) := (P₀ : Subgroup (N t)).map (N t).subtype with hQ₀
  have hQ₀p : IsPGroup ℓ Q₀ := P₀.isPGroup'.map _
  have hQ₀i : ¬ ℓ ∣ Q₀.index := by
    rw [hQ₀, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h2 | h2
    · exact P₀.not_dvd_index h2
    · exact hℓNindex h2
  set Q : Sylow ℓ (C t) := hQ₀p.toSylow hQ₀i with hQdef
  have hQeq : (Q : Subgroup (C t)) = Q₀ := IsPGroup.toSylow_coe hQ₀p hQ₀i
  have hQN : ∀ x ∈ (Q : Subgroup (C t)), x ∈ N t := by
    intro x hx
    rw [hQeq] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hQnormal : (Q : Subgroup (C t)).Normal := by
    have hP₀n : (P₀ : Subgroup (N t)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hc : g * x = x * g := Subtype.ext (hNcomm _ g.2 _ x.2)
      rw [hc, mul_inv_cancel_right]
      exact hx
    have : (P₀ : Subgroup (N t)).Characteristic := Sylow.characteristic_of_normal P₀ hP₀n
    have : (N t).Normal := Subgroup.normal_of_characteristic _
    rw [hQeq, hQ₀]
    infer_instance
  have hQbot : (Q : Subgroup (C t)) ≠ ⊥ := by
    apply Q.ne_bot_of_dvd_card
    exact hℓN.trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQbot
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hYQ : Y ≤ Subgroup.centralizer (Q : Set (C t)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hYcent hc)) x (hQN x hx)
  have hQY : Subgroup.centralizer (Q : Set (C t)) = Y := by
    set sC : C t := ⟨s₀, hsC⟩ with hsCdef
    have hsQ : sC ∉ Subgroup.centralizer (Q : Set (C t)) := by
      intro hsc
      have h1 : sC * x₀ = x₀ * sC := (Subgroup.mem_centralizer_iff.mp hsc x₀ hx₀).symm
      have h2 := hNainv (x₀ : G) ⟨x₀, hQN x₀ hx₀, rfl⟩
      have h3 : (x₀ : G) = (x₀ : G)⁻¹ := by
        rw [← h2]
        have h1' := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul, hsCdef] at h1'
        rw [h1', mul_inv_cancel_right]
      have hodd : Odd (orderOf (x₀ : G)) := by
        rw [Subgroup.orderOf_coe]
        exact hNodd.of_dvd_nat (by
          have h := Subgroup.orderOf_dvd_natCard (N t) (hQN x₀ hx₀)
          exact h)
      exact hx₀1' (Subtype.ext (StationaryConfinement.eq_one_of_eq_inv_of_odd hodd h3))
    have hsY : sC ∉ Y := fun h => hsQ (hYQ h)
    apply le_antisymm _ hYQ
    intro c hc
    by_contra hcY
    have hmul : c⁻¹ * sC ∈ Y := by
      rw [Subgroup.mul_mem_iff_of_index_two hY]
      exact iff_of_false (fun h => hcY (by simpa using Y.inv_mem h)) hsY
    exact hsQ (by
      have := Subgroup.mul_mem _ hc (hYQ hmul)
      rwa [mul_inv_cancel_left] at this)
  set Qa : Subgroup G := (Q : Subgroup (C t)).map (C t).subtype with hQa
  have hQaNa : Qa ≤ Na := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hQN x hx, rfl⟩
  have hQabot : Qa ≠ ⊥ := by
    rw [Ne, hQa, Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective]
    exact hQbot
  refine ⟨Q, hQaNa, hQnormal, ?_, hQY, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    exact hNcomm x (hQN x hx) y (hQN y hy)
  ·
    intro x hx
    exact hNainv (x : G) ⟨x, hQN x hx, rfl⟩
  ·
    have hNaC : Na ≤ C t := Subgroup.map_subtype_le _
    have hNacard : Nat.card Na = Nat.card (N t) :=
      Subgroup.card_map_of_injective (C t).subtype_injective
    have hNaodd : Odd (Nat.card Na) := hNacard ▸ hNodd
    have hNanormal : (Na.subgroupOf (C t)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNaC).mpr
        (StationaryConfinement.le_normalizer_map_of_normal (C t) (N t))
    obtain ⟨hloc, -⟩ :=
      Principal.confined_normal_inverted_odd_subgroup_primes_do_not_divide_centralizer_index
        n hn S fS t ht Na hNaC hNaodd hNanormal hNainv hcent3
    obtain ⟨P₁⟩ : Nonempty (Sylow ℓ Na) := inferInstance
    exact (hloc ℓ hℓ (hNacard ▸ hℓN) P₁).2 Q
  ·
    intro u hu hu1
    exact hnorm3 (u : G) ⟨u, hQN u hu, rfl⟩ (fun h => hu1 (Subtype.ext h))
  ·
    apply le_antisymm _ (StationaryConfinement.le_normalizer_map_of_normal (C t) Q)
    intro g hg
    by_contra hgC
    apply hQabot
    rw [eq_bot_iff, ← hTI g hgC]
    intro x hx
    refine ⟨hQaNa hx, g⁻¹ * x * g, hQaNa ((Subgroup.mem_normalizer_iff''.mp hg x).mp hx), ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  ·
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ C t := hcent3 (x₀ : G) ⟨x₀, hQN x₀ hx₀, rfl⟩
        (fun h => hx₀1' (Subtype.ext h))
        (Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hx (x₀ : G) ⟨x₀, hx₀, rfl⟩)).symm)
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, ← hQY, Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : G) ⟨y, hy, rfl⟩)
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hQY] at hy
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy x hx)

end CFSG.Semidihedral.FixedCoreNontrivialPrimes
