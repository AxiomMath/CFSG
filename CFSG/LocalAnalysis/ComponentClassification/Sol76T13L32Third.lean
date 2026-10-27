module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Kernel
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Count
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Sylow

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def Lemma32ConditionTwoInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 → ∀ K ∈ kStarComponents N, ∀ K₀ ∈ kStarComponents N, K ≠ K₀ →
    ∀ b ∈ K, orderOf b = 2 → b ∉ coreActionKernel K →
      (kStarComponents (centralizer ({b} : Set G))).ncard = 2 →
      (∀ M ∈ kStarComponents (centralizer ({b} : Set G)),
        ¬ twoLayerIn (K₀ ⊓ centralizer ({b} : Set G)) ≤ coreActionKernel M ∧ b ∈ M) →
      ∃ M ∈ kStarComponents (centralizer ({b} : Set G)),
        3 ≤ CFSG.pRank 2 ↥((oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
          twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup {P O : Subgroup G} (hP : IsPGroup 2 P)
    (hO : Nat.Coprime 2 (Nat.card O)) {c : G} (hcP : c ∈ P) (hcO : c ∈ O) : c = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
  have h1 : orderOf c ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf c ∣ Nat.card O := by
    have h3 := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
    rwa [Subgroup.orderOf_mk] at h3
  have h4 : Nat.Coprime (2 ^ k) (Nat.card O) := Nat.Coprime.pow_left k hO
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h1 h2)

theorem two_le_ncard_kStarComponents {N : Subgroup G} (hN : IsKBalanced N) :
    2 ≤ (kStarComponents N).ncard := by
  obtain ⟨r, Kf, hinj, hiff, h2r, -⟩ := hN
  have hmem : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  have hne : Kf ⟨0, by omega⟩ ≠ Kf ⟨1, h2r⟩ := fun h => by
    have := hinj h
    simp at this
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard (Set.insert_subset (hmem _) (Set.singleton_subset_iff.mpr (hmem _)))

theorem four_mul_card_inf_coreActionKernel_le (hq : QuasisimpleTwoPartInput) {H K : Subgroup G}
    (hK : IsTwoComponentIn K H)
    (hcat : Blueprint.Catalog ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)))
    {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (hbQ : b ∉ coreActionKernel K) {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSK : S ≤ K)
    (hcard : Nat.card S = 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2) :
    4 * Nat.card ↥(S ⊓ coreActionKernel K) ≤ Nat.card S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    pPrimeCore_coprime_card (p := 2) (G := ↥K)
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp hOcop
  have hQq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hK.1 hK.2
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have ht2 : (⟨b, hbK⟩ : ↥K) * ⟨b, hbK⟩ = 1 := Subtype.ext hbb
  have hx1 : ((⟨b, hbK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) ≠ 1 := by
    intro h
    have hO : (⟨b, hbK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h
    have h1 := orderOf_dvd_natCard (⟨⟨b, hbK⟩, hO⟩ : pPrimeCore 2 ↥K)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb2] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd hOcop h1) (by norm_num)
  have hx2 : orderOf ((⟨b, hbK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]) hx1
  have hxc : ((⟨b, hbK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    intro hZ
    apply hbQ
    refine ⟨le_normalizer hbK, fun k hk => ?_⟩
    have h1 := (mem_center_iff.mp hZ) ((⟨k, hk⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)
    exact (mk_mul_comm_iff (N := K) ⟨k, hk⟩ ⟨b, hbK⟩).mp h1
  have hcl := hq.2 (↥K ⧸ pPrimeCore 2 ↥K) hQq hcat _ hx2 hxc
  have hdvdC : Nat.card ↥(centralizer ({((⟨b, hbK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)} :
      Set (↥K ⧸ pPrimeCore 2 ↥K))) ∣ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
    have h1 := CFSG.Walter.Suzuki.centralizer_mk_le_map (pPrimeCore 2 ↥K) hOodd ht2
    have h2 : (centralizer ({(⟨b, hbK⟩ : ↥K)} : Set ↥K)).map K.subtype ≤
        K ⊓ centralizer ({b} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨y.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    refine (card_dvd_of_le h1).trans ?_
    rw [← relIndex_ker]
    refine (relIndex_dvd_card _ _).trans ?_
    rw [← card_map_of_injective K.subtype_injective]
    exact card_dvd_of_le h2
  have hSQK : S ⊓ coreActionKernel K ≤ K := inf_le_left.trans hSK
  have hAp : IsPGroup 2 ((S ⊓ coreActionKernel K).subgroupOf K) :=
    (hS2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hSQK).symm
  have hAcard : Nat.card ((S ⊓ coreActionKernel K).subgroupOf K) =
      Nat.card ↥(S ⊓ coreActionKernel K) :=
    Nat.card_congr (subgroupOfEquivOfLe hSQK).toEquiv
  have hker : Nat.card ↥((QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker ⊓
      (S ⊓ coreActionKernel K).subgroupOf K) = 1 := by
    rw [QuotientGroup.ker_mk', ← eq_bot_iff_card, eq_bot_iff]
    rintro y ⟨hyO, hyA⟩
    exact (mem_bot).mpr (eq_one_of_mem_of_isPGroup hAp hOcop hyA hyO)
  have hmapcard : Nat.card ↥(((S ⊓ coreActionKernel K).subgroupOf K).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥K))) =
      Nat.card ((S ⊓ coreActionKernel K).subgroupOf K) := by
    have h := relIndex_mul_card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker
      ((S ⊓ coreActionKernel K).subgroupOf K)
    rw [hker, mul_one, relIndex_ker] at h
    exact h
  have hAZ : ((S ⊓ coreActionKernel K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) ≤
      center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ S ⊓ coreActionKernel K := mem_subgroupOf.mp ha
    rw [mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) z
    exact (mk_mul_comm_iff (N := K) k a).mpr ((mem_inf.mp ha').2.2 k k.2)
  have hdvdZ : Nat.card ↥(S ⊓ coreActionKernel K) ∣
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := by
    rw [← hAcard, ← hmapcard]
    exact card_dvd_of_le hAZ
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hS2.to_le (inf_le_left : S ⊓ coreActionKernel K ≤ S))
  have hjZ : j ≤ (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (hj ▸ hdvdZ)
  have hCK : (Nat.card ↥(centralizer ({((⟨b, hbK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)} :
      Set (↥K ⧸ pPrimeCore 2 ↥K)))).factorization 2 ≤
      (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdC 2
  rw [hj, hcard, show 4 * 2 ^ j = 2 ^ (j + 2) by ring]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isKBalanced_centralizer_of_two {𝒜 : Thm13Ambient} (hq : QuasisimpleTwoPartInput)
    (hKK : KStarKProper G) (hR1 : Lemma32ConditionTwoInputFor 𝒜) (hG : 𝒜 G) {N K K₀ : Subgroup G}
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK₀ : K₀ ∈ kStarComponents N)
    (hKK₀ : K ≠ K₀) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2) (hbQ : b ∉ coreActionKernel K)
    (hpump : (pumpSet K₀ (centralizer ({b} : Set G))).ncard = 2)
    (hnc : (kStarComponents (centralizer ({b} : Set G))).ncard = (kStarComponents N).ncard) :
    IsKBalanced (centralizer ({b} : Set G)) := by
  classical
  by_cases hr3 : 3 ≤ (kStarComponents N).ncard
  · exact isKBalanced_of_three_le_ncard hq hKK (hnc ▸ hr3)
  have hr : (kStarComponents N).ncard = 2 := by
    have := two_le_ncard_kStarComponents hN.1
    omega
  have hCr : (kStarComponents (centralizer ({b} : Set G))).ncard = 2 := hnc.trans hr
  have heqP : pumpSet K₀ (centralizer ({b} : Set G)) =
      kStarComponents (centralizer ({b} : Set G)) :=
    Set.eq_of_subset_of_ncard_le (fun M hM => hM.1) (by rw [hpump, hCr]) (Set.toFinite _)
  have hbC : b ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hcent : ∀ n ∈ centralizer ({b} : Set G), n * b = b * n := fun n hn =>
    mem_centralizer_singleton_iff.mp hn
  have hbO : b ∈ oddTwoCoreIn (centralizer ({b} : Set G)) :=
    mem_oddTwoCoreIn_of_central hbC hcent hb2
  obtain ⟨Kf, hinj, hiff⟩ := exists_enum_kStarComponents (centralizer ({b} : Set G))
  have hKf : ∀ i, Kf i ∈ kStarComponents (centralizer ({b} : Set G)) := fun i =>
    (hiff (Kf i)).mpr ⟨i, rfl⟩
  refine ⟨_, Kf, hinj, hiff, by omega, fun i j hij => ?_, ?_, Or.inr (Or.inl ?_)⟩
  · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  · suffices h : ∃ M ∈ kStarComponents (centralizer ({b} : Set G)),
        3 ≤ CFSG.pRank 2 ↥((oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
          twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M) by
      obtain ⟨M, hM, h3⟩ := h
      obtain ⟨i, hi⟩ := (hiff M).mp hM
      exact ⟨i, hi ▸ h3⟩
    by_cases hall : ∀ M ∈ kStarComponents (centralizer ({b} : Set G)), b ∈ M
    · refine hR1 G hG N hN hr K hK K₀ hK₀ hKK₀ b hbK hb2 hbQ hCr fun M hM => ⟨?_, hall M hM⟩
      rw [← heqP] at hM
      exact hM.2
    push Not at hall
    obtain ⟨M₀, hM₀, hbM₀⟩ := hall
    obtain ⟨M₁, hM₁, hne⟩ := Set.exists_ne_of_one_lt_ncard
      (show 1 < (kStarComponents (centralizer ({b} : Set G))).ncard by omega) M₀
    refine ⟨M₁, hM₁, ?_⟩
    have hle : M₀ ≤ (oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
        twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M₁ :=
      le_inf ((le_twoLayerIn_of_isTwoComponentIn hM₀.1).trans le_sup_right)
        (GSThmB.B5a.le_coreActionKernel_of_ne hM₁.1.1 hM₀.1.1 hM₁.1.2 hM₀.1.2 hne)
    have hbX : b ∈ (oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
        twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel M₁ :=
      mem_inf.mpr ⟨mem_sup_left hbO, mem_coreActionKernel_of_le_centralizer hM₁.1.1⟩
    have h3 := pRank_succ_le_of_commute hle hbX hb2 (fun y hy => hcent y (hM₀.1.1 hy)) hbM₀
    have h2 := two_le_pRank_of_mem_solomonKStar hM₀.2
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    omega
  · have hbY : b ∈ (oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
        twoLayerIn (centralizer ({b} : Set G))) ⊓
        coreActionKernel (solomonKStarOf (centralizer ({b} : Set G))) :=
      mem_inf.mpr ⟨mem_sup_left hbO, mem_coreActionKernel_of_le_centralizer (solomonKStarOf_le _)⟩
    exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨b, hbY⟩)
      (by rw [Subgroup.orderOf_mk]; exact hb2)

theorem false_of_two_le_ncard_pumpSet {𝒜 : Thm13Ambient} (hq : QuasisimpleTwoPartInput)
    (hKK : KStarKProper G) (hR1 : Lemma32ConditionTwoInputFor 𝒜) (hG : 𝒜 G)
    (hv : ∀ N' : Subgroup G, IsKBalanced N' →
      ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G))
    {N K K₀ : Subgroup G} (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK₀ : K₀ ∈ kStarComponents N) (hKK₀ : K ≠ K₀) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (h2 : 2 ≤ (pumpSet K₀ (centralizer ({b} : Set G))).ncard) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK₀2, hone, hnc, hexh⟩ :=
    two_pumpSet_structure hq hKK hN hK hK₀ hKK₀ hbK hb2 (hv _) h2
  have hbQ : b ∉ coreActionKernel K := by
    intro hbQ
    obtain ⟨M, hM⟩ := pumpSet_nonempty hK hbQ hb2
    obtain ⟨K', hK', hK'K, hMK'⟩ := hexh M hM.1
    exact Set.disjoint_left.mp (pumpSet_disjoint hK hK' (Ne.symm hK'K) hbQ
      (mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) hbK) hb2) hM hMK'
  have hbD : b ∉ kStarKernel N := fun h => hbQ (kStarKernel_le_coreActionKernel hK h)
  have hCbal :=
    isKBalanced_centralizer_of_two hq hKK hR1 hG hN hK hK₀ hKK₀ hbK hb2 hbQ hK₀2 hnc
  have hmeas := kernel_measure_le_of_isSolomonChoice hN hCbal (hv _ hCbal) hnc
  have hbKC : b ∈ K ⊓ centralizer ({b} : Set G) :=
    mem_inf.mpr ⟨hbK, mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨S, hSKC, hbS, hS2, hScard⟩ : ∃ S : Subgroup G,
      S ≤ K ⊓ centralizer ({b} : Set G) ∧ b ∈ S ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 := by
    have hbz : IsPGroup 2 (zpowers (⟨b, hbKC⟩ : ↥(K ⊓ centralizer ({b} : Set G)))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb2, pow_one])
    obtain ⟨Sy, hSy⟩ := hbz.exists_le_sylow
    refine ⟨(Sy : Subgroup ↥(K ⊓ centralizer ({b} : Set G))).map
      (K ⊓ centralizer ({b} : Set G)).subtype, map_subtype_le _,
      ⟨⟨b, hbKC⟩, hSy (mem_zpowers _), rfl⟩, Sy.isPGroup'.map _, ?_⟩
    rw [card_map_of_injective (Subgroup.subtype_injective _), Sy.card_eq_multiplicity]
  have hSK : S ≤ K := hSKC.trans inf_le_left
  have hSN : S ≤ normalizer (kStarKernel N : Set G) := fun s hs =>
    le_normalizer_kStarKernel N (hK.1.1 (hSK hs))
  obtain ⟨P, hPD, hP2, hPcard, hPS, hPrank⟩ : ∃ P : Subgroup G, P ≤ kStarKernel N ∧
      IsPGroup 2 P ∧ Nat.card P = 2 ^ (Nat.card ↥(kStarKernel N)).factorization 2 ∧
      S ≤ normalizer (P : Set G) ∧ CFSG.pRank 2 ↥(kStarKernel N) ≤ CFSG.Open.pRank 2 P := by
    obtain ⟨Py, hPy⟩ := exists_sylow_normalized hSN hS2
    refine ⟨(Py : Subgroup ↥(kStarKernel N)).map (kStarKernel N).subtype, map_subtype_le _,
      Py.isPGroup'.map _, ?_, hPy, ?_⟩
    · rw [card_map_of_injective (Subgroup.subtype_injective _), Py.card_eq_multiplicity]
    · rw [← (SectionRank.pRank_sylow Py).2, SectionRank.pRank_eq_open_pRank_top,
        ← SectionRank.pRank_eq_pRank_top_subgroup]
      exact SectionRank.pRank_le_map (by norm_num) _ (Subgroup.subtype_injective _) _
  have hPScomm : ∀ p ∈ P, ∀ s ∈ S, p * s = s * p := by
    intro p hp s hs
    have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
    have h1 : s⁻¹ * p⁻¹ * s * p ∈ oddCoreIn (solomonKStarOf N) :=
      (mem_inf.mp (hPD hp)).2.2 s (hKD (hSK hs))
    have h2 : s⁻¹ * p⁻¹ * s * p ∈ P := by
      have h3 : s⁻¹ * p⁻¹ * s⁻¹⁻¹ ∈ P :=
        (mem_normalizer_iff.mp (hPS (inv_mem hs)) p⁻¹).mp (inv_mem hp)
      rw [inv_inv] at h3
      exact mul_mem h3 hp
    have h4 := eq_one_of_mem_of_isPGroup hP2 (coprime_card_oddCoreIn _) h2 h1
    have h5 : p * s = p * s * (s⁻¹ * p⁻¹ * s * p) := by rw [h4, mul_one]
    rw [h5]
    group
  have hPC : P ≤ centralizer ({b} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (hPScomm p hp b hbS)
  have hYC : P ⊔ S ≤ centralizer ({b} : Set G) := sup_le hPC (hSKC.trans inf_le_right)
  have hYp : IsPGroup 2 ↥(P ⊔ S) := hP2.to_sup_of_normal_left' hS2 hPS
  have hYQ : ∀ K' ∈ kStarComponents N, K' ≠ K → P ⊔ S ≤ coreActionKernel K' :=
    fun K' hK' hK'K => sup_le (hPD.trans (kStarKernel_le_coreActionKernel hK'))
      fun s hs => mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) (hSK hs)
  have hYpump : ∀ K' ∈ kStarComponents N, K' ≠ K → ∀ g ∈ P ⊔ S,
      ∀ M ∈ pumpSet K' (centralizer ({b} : Set G)),
        M.map (MulAut.conj g).toMonoidHom ∈ pumpSet K' (centralizer ({b} : Set G)) :=
    fun K' hK' hK'K g hg _ hM =>
      map_conj_mem_pumpSet (le_normalizer (hYC hg)) (hYQ K' hK' hK'K hg).1 hM
  have hodd : ∀ K' ∈ kStarComponents N, K' ≠ K → ∀ R : Subgroup G, R ≤ P ⊔ S →
      ¬ 2 ∣ Nat.card ↥⁅R, twoLayerIn (K' ⊓ centralizer ({b} : Set G))⁆ := by
    intro K' hK' hK'K R hRY h
    obtain ⟨hY2, -, -, -, -⟩ :=
      pump_facts hK' (mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) hbK) hb2
    have hle : ⁅R, twoLayerIn (K' ⊓ centralizer ({b} : Set G))⁆ ≤ oddCoreIn K' := by
      refine commutator_le.mpr fun r hr k hk => ?_
      have hkK' : k ∈ K' := (hY2.1.trans inf_le_left) hk
      have h1 : (k⁻¹)⁻¹ * (r⁻¹)⁻¹ * k⁻¹ * r⁻¹ ∈ oddCoreIn K' :=
        (inv_mem (hYQ K' hK' hK'K (hRY hr))).2 k⁻¹ (inv_mem hkK')
      have h2 : ⁅r, k⁆ = ((k⁻¹)⁻¹ * (r⁻¹)⁻¹ * k⁻¹ * r⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact inv_mem h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn K')
      (h.trans (card_dvd_of_le hle))
  obtain ⟨A₁, A₂, hA, hpair⟩ := Set.ncard_eq_two.mp hK₀2
  have hYA : ∀ g ∈ P ⊔ S, ∀ A : Subgroup G, (A = A₁ ∨ A = A₂) →
      (A.map (MulAut.conj g).toMonoidHom = A₁ ∨ A.map (MulAut.conj g).toMonoidHom = A₂) := by
    intro g hg A hA'
    have hAm : A ∈ pumpSet K₀ (centralizer ({b} : Set G)) := by
      rw [hpair]
      rcases hA' with rfl | rfl <;> simp
    have h1 := hYpump K₀ hK₀ (Ne.symm hKK₀) g hg A hAm
    rw [hpair] at h1
    simpa using h1
  have hidx : (normalizer (A₁ : Set G)).relIndex (P ⊔ S) ≤ 2 := relIndex_normalizer_le_two hA hYA
  have hXN : ∀ M ∈ kStarComponents (centralizer ({b} : Set G)),
      (P ⊔ S) ⊓ normalizer (A₁ : Set G) ≤ normalizer (M : Set G) := by
    intro M hM x hx
    obtain ⟨hxY, hxA⟩ := mem_inf.mp hx
    obtain ⟨K', hK', hK'K, hMK'⟩ := hexh M hM
    by_cases hK'0 : K' = K₀
    · rw [hK'0, hpair] at hMK'
      rcases hMK' with rfl | hM2
      · exact hxA
      rw [Set.mem_singleton_iff] at hM2
      subst hM2
      have hxA' : A₁.map (MulAut.conj x).toMonoidHom = A₁ := mem_normalizer_iff_map_conj_eq.mp hxA
      rcases hYA x hxY _ (Or.inr rfl) with h | h
      · exact absurd (Subgroup.map_injective (MulAut.conj x).injective (h.trans hxA'.symm))
          (Ne.symm hA)
      · exact mem_normalizer_iff_map_conj_eq.mpr h
    · obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp (hone K' hK' hK'K hK'0)
      have hMM' : M = M' := by
        rw [hM'] at hMK'
        exact Set.mem_singleton_iff.mp hMK'
      have h1 := hYpump K' hK' hK'K x hxY M hMK'
      rw [hM', ← hMM'] at h1
      exact mem_normalizer_iff_map_conj_eq.mpr (Set.mem_singleton_iff.mp h1)
  have hXker : (P ⊔ S) ⊓ normalizer (A₁ : Set G) ≤ kStarKernel (centralizer ({b} : Set G)) := by
    intro x hx
    have hxC : x ∈ centralizer ({b} : Set G) := hYC (mem_inf.mp hx).1
    refine mem_inf.mpr ⟨hxC, mem_coreActionKernel_solomonKStarOf hxC fun M hM => ?_⟩
    obtain ⟨K', hK', hK'K, hMK'⟩ := hexh M hM
    have hbQ' := mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) hbK
    obtain ⟨hY2, -, ⟨e⟩, h212, -⟩ := pump_facts hK' hbQ' hb2
    have hYL : twoLayerIn (K' ⊓ centralizer ({b} : Set G)) ≤
        twoLayerIn (centralizer ({b} : Set G)) :=
      h212.trans (solomonKStarOf_le_twoLayerIn _)
    have ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) =
        Nat.card (↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G))) ⧸
          Open.fusionZStar ↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G)))) := by
      rw [card_fusionZStar_of_mem_pumpSet hK' hbQ' hb2 hMK', Nat.card_congr e.toEquiv]
    exact le_coreActionKernel_of_odd_commutator hM.1 hYL
      (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
      (isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2) hMK'.2 ht
      (inf_le_left.trans hYC) (hXN M hM) (hodd K' hK' hK'K _ inf_le_left) hx
  have hbX : b ∈ (P ⊔ S) ⊓ normalizer (A₁ : Set G) := by
    have hA₁ : A₁ ∈ pumpSet K₀ (centralizer ({b} : Set G)) := by
      rw [hpair]
      simp
    exact mem_inf.mpr ⟨mem_sup_right hbS, (mem_coreActionKernel_of_le_centralizer hA₁.1.1.1).1⟩
  have hneY : (normalizer (A₁ : Set G)).relIndex (P ⊔ S) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos (relIndex_dvd_card _ _) Nat.card_pos)
  have hrankB := pRank_le_pRank_inf_add_one ((relIndex_le_of_le_right le_sup_left hneY).trans hidx)
  have hrankX := pRank_succ_le_of_commute (inf_le_inf_right _ le_sup_left) hbX hb2
    (fun y hy => hPScomm y (mem_inf.mp hy).1 b hbS) fun h => hbD (hPD (mem_inf.mp h).1)
  have hrankK := SectionRank.pRank_mono (by norm_num : 1 < 2) hXker
  have hrankC : CFSG.pRank 2 ↥(kStarKernel (centralizer ({b} : Set G))) =
      CFSG.Open.pRank 2 (kStarKernel (centralizer ({b} : Set G))) := by
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
  have he2 := hmeas.2 (le_antisymm hmeas.1 (by omega))
  have hXcard : Nat.card ↥((P ⊔ S) ⊓ normalizer (A₁ : Set G)) ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hYp.to_le (inf_le_left :
      (P ⊔ S) ⊓ normalizer (A₁ : Set G) ≤ P ⊔ S))
    have hkle : k ≤ (Nat.card ↥(kStarKernel (centralizer ({b} : Set G)))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        (hk ▸ card_dvd_of_le hXker)
    rw [hk, hPcard]
    exact Nat.pow_le_pow_right (by norm_num) (hkle.trans he2)
  have hYX : Nat.card ↥(P ⊔ S) ≤ 2 * Nat.card ↥((P ⊔ S) ⊓ normalizer (A₁ : Set G)) := by
    have h := relIndex_mul_card (normalizer (A₁ : Set G)) (P ⊔ S)
    rw [inf_comm] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx
  have hPY : P.relIndex (P ⊔ S) ≤ 2 := by
    have h := relIndex_mul_card P (P ⊔ S)
    rw [inf_of_le_left le_sup_left] at h
    have h3 : P.relIndex (P ⊔ S) * Nat.card P ≤ 2 * Nat.card P := by
      rw [h]
      exact hYX.trans (Nat.mul_le_mul_left 2 hXcard)
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  have hneP : P.relIndex (P ⊔ S) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos (relIndex_dvd_card _ _) Nat.card_pos)
  have hS2P : Nat.card S ≤ 2 * Nat.card ↥(P ⊓ S) := by
    have h := relIndex_mul_card P S
    rw [← h]
    exact Nat.mul_le_mul_right _ ((relIndex_le_of_le_right le_sup_right hneP).trans hPY)
  have hR2 := four_mul_card_inf_coreActionKernel_le hq hK.1
    (catalog_coreQuotient_of_mem_solomonKStar hKK hK.1 hK.2) hbK hb2 hbQ hS2 hSK hScard
  have hPS' : Nat.card ↥(P ⊓ S) ≤ Nat.card ↥(S ⊓ coreActionKernel K) := by
    refine card_le_of_le ?_
    rw [inf_comm]
    exact inf_le_inf_left _ (hPD.trans (kStarKernel_le_coreActionKernel hK))
  have hpos : 0 < Nat.card ↥(S ⊓ coreActionKernel K) := Nat.card_pos
  omega

end CFSG.ComponentClassification.Sol76T13
