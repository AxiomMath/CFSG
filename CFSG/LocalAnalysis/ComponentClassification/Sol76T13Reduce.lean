module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Third

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

theorem four_dvd_card_centralizer_of_perfect {Q : Type} [Group Q] [Finite Q]
    [Group.IsPerfect Q] {x : Q} (hx : orderOf x = 2) :
    4 ∣ Nat.card ↥(centralizer ({x} : Set Q)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite Q
  by_contra h4
  set C := centralizer ({x} : Set Q) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have h2C : 2 ∣ Nat.card C := by
    have h := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    rwa [Subgroup.orderOf_mk, hx] at h
  have hv : (Nat.card C).factorization 2 ≤ 1 := by
    by_contra h2
    apply h4
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr
      (show 2 ≤ (Nat.card C).factorization 2 by omega)
    rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
  set X := zpowers x with hX
  have hXcard : Nat.card X = 2 := by rw [hX, Nat.card_zpowers, hx]
  have hX2 : IsPGroup 2 X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  obtain ⟨T, hXT⟩ := hX2.exists_le_sylow
  have hxT : x ∈ (T : Subgroup Q) := hXT (mem_zpowers x)
  have hXC : X ≤ C := by rw [hX, zpowers_le]; exact hxC
  have hTC : X = (T : Subgroup Q) ⊓ C := by
    refine eq_of_le_of_card_ge (le_inf hXT hXC) ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      ((T.isPGroup').to_le (inf_le_left : (T : Subgroup Q) ⊓ C ≤ T))
    have hdvd : 2 ^ k ∣ Nat.card C :=
      hk ▸ card_dvd_of_le (inf_le_right : (T : Subgroup Q) ⊓ C ≤ C)
    have hk1 : k ≤ 1 :=
      ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd).trans hv
    rw [hk, hXcard]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := pow_one 2
  have hne : (⟨x, hxT⟩ : ↥(T : Subgroup Q)) ≠ 1 := fun h => by
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have : Nontrivial ↥(T : Subgroup Q) := ⟨⟨_, _, hne⟩⟩
  have : Nontrivial ↥(center ↥(T : Subgroup Q)) := (T.isPGroup').center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(center ↥(T : Subgroup Q)))
  have hzX : ((z : ↥(T : Subgroup Q)) : Q) ∈ X := by
    rw [hTC]
    refine mem_inf.mpr ⟨(z : ↥(T : Subgroup Q)).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h := (mem_center_iff.mp z.2) ⟨x, hxT⟩
    exact (congrArg Subtype.val h).symm
  have hz1 : ((z : ↥(T : Subgroup Q)) : Q) ≠ 1 := fun h =>
    hz (Subtype.ext (Subtype.ext h))
  have hzx : ((z : ↥(T : Subgroup Q)) : Q) = x := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hzX
    have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exfalso
      apply hz1
      rw [← hn, ← two_mul, zpow_mul, show x ^ (2 : ℤ) = 1 by
        rw [zpow_two, hxx], one_zpow]
    · rw [← hn, zpow_add, zpow_mul, show x ^ (2 : ℤ) = 1 by rw [zpow_two, hxx], one_zpow,
        one_mul, zpow_one]
  have hTle : (T : Subgroup Q) ≤ C := by
    intro t ht
    refine mem_centralizer_singleton_iff.mpr ?_
    have h : t * ((z : ↥(T : Subgroup Q)) : Q) = ((z : ↥(T : Subgroup Q)) : Q) * t :=
      congrArg Subtype.val ((mem_center_iff.mp z.2) ⟨t, ht⟩)
    rw [hzx] at h
    exact h
  have hTX : (T : Subgroup Q) = X := by
    rw [hTC]
    exact (inf_eq_left.mpr hTle).symm
  have hTcard : Nat.card ↥(T : Subgroup Q) = 2 := by rw [hTX, hXcard]
  have hcyc : IsCyclic ↥(T : Subgroup Q) := isCyclic_of_prime_card hTcard
  have heven : Even (Fintype.card Q) := by
    rw [← Nat.card_eq_fintype_card]
    have h := orderOf_dvd_natCard x
    rw [hx] at h
    exact even_iff_two_dvd.mpr h
  obtain ⟨-, -, -, hidx⟩ := LinearGroups.cyclic_sylow_index_two heven T hcyc
  have hker := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign.comp (MulAction.toPermHom Q Q))
  rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hker
  rw [hker, index_top] at hidx
  norm_num at hidx

@[expose] def QuasisimpleEvenCenterInput : Prop :=
  (∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Blueprint.Catalog (Q ⧸ center Q) →
    ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u ≠ v → u ∈ center Q → v ∈ center Q →
      ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Blueprint.Catalog (Q ⧸ center Q) →
    2 ∣ Nat.card ↥(center Q) → ∀ x : Q, orderOf x = 2 → x ∉ center Q →
      (Nat.card ↥(center Q)).factorization 2 + 2 ≤
        (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2

theorem quasisimpleTwoPartInput_of_evenCenter (h : QuasisimpleEvenCenterInput) :
    QuasisimpleTwoPartInput := by
  refine ⟨h.1, fun Q _ _ hQ hcat x hx hxZ => ?_⟩
  by_cases h2 : 2 ∣ Nat.card ↥(center Q)
  · exact h.2 Q hQ hcat h2 x hx hxZ
  · have : Group.IsPerfect Q := hQ.1
    have h0 : (Nat.card ↥(center Q)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd h2
    have h4 : 2 ^ 2 ∣ Nat.card ↥(centralizer ({x} : Set Q)) := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact four_dvd_card_centralizer_of_perfect hx
    have h5 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h4
    omega

@[expose] def Lemma32ConditionTwoRankTwoInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 → ∀ K ∈ kStarComponents N, ∀ K₀ ∈ kStarComponents N, K ≠ K₀ →
    ∀ b ∈ K, orderOf b = 2 → b ∉ coreActionKernel K →
      (kStarComponents (centralizer ({b} : Set G))).ncard = 2 →
      (∀ M ∈ kStarComponents (centralizer ({b} : Set G)),
        ¬ twoLayerIn (K₀ ⊓ centralizer ({b} : Set G)) ≤ coreActionKernel M ∧ b ∈ M ∧
          CFSG.pRank 2 ↥M = 2) →
      ∃ M ∈ kStarComponents (centralizer ({b} : Set G)),
        3 ≤ CFSG.pRank 2 ↥((oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
          twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M)

theorem lemma32ConditionTwoInputFor_of_rankTwo {𝒜 : Thm13Ambient}
    (h : Lemma32ConditionTwoRankTwoInputFor 𝒜) : Lemma32ConditionTwoInputFor 𝒜 := by
  intro G _ _ hG N hN hr K hK K₀ hK₀ hKK₀ b hbK hb2 hbQ hCr hall
  by_cases h3 : ∃ M ∈ kStarComponents (centralizer ({b} : Set G)), 3 ≤ CFSG.pRank 2 ↥M
  · obtain ⟨M, hM, hM3⟩ := h3
    obtain ⟨M', hM', hne⟩ := Set.exists_ne_of_one_lt_ncard
      (show 1 < (kStarComponents (centralizer ({b} : Set G))).ncard by omega) M
    refine ⟨M', hM', ?_⟩
    have hle : M ≤ (oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
        twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M' :=
      le_inf ((le_twoLayerIn_of_isTwoComponentIn hM.1).trans le_sup_right)
        (GSThmB.B5a.le_coreActionKernel_of_ne hM'.1.1 hM.1.1 hM'.1.2 hM.1.2 hne)
    have hmono := SectionRank.pRank_mono (by norm_num : 1 < 2) hle
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hM3
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  · push Not at h3
    refine h G hG N hN hr K hK K₀ hK₀ hKK₀ b hbK hb2 hbQ hCr fun M hM =>
      ⟨(hall M hM).1, (hall M hM).2, ?_⟩
    have h2 := two_le_pRank_of_mem_solomonKStar hM.2
    have h3M := h3 M hM
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h3M
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    omega

end CFSG.ComponentClassification.Sol76T13
