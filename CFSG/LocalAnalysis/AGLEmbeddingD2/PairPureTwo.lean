module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureOne
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairRankBook

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_barM {M E : Subgroup G} {q : ℕ} (hE : IsElemAbelian q E) :
    IsElemAbelian q (barM M E) := by
  have hE' : IsElemAbelian q (E.subgroupOf M) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (hE.1.is_comm.comm ⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩)
      exact this
    · simpa using hE.2 (x : G) hx
  exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map q hE' _

theorem AGLPair.false_of_three_weakSBlock_images (h : AGLPair 3 M H R)
    (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    (L : Fin 3 → Subgroup G) (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i))
    (hne : Function.Injective fun i => barM M (L i)) : False := by
  have hz : ∀ i : Fin 3, ∃ y ∈ barM M (L i),
      y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
        IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ barM M (L i), y * l ≠ l * y := by
    intro i
    obtain ⟨y, ⟨hyN, hyL⟩, hy3, l, hl, hyl⟩ := hthree (L i) (hL i)
    exact ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyN),
      isPGroup_zpowers_mk _ hy3, _, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl),
      barM_not_commute (hL i).le hyL hl hyl⟩
  choose y hyL hyK hy3 hyZ using hz
  have hrank := le_pRank_of_components Nat.prime_three (fun i => barM M (L i))
    (fun i => (hL i).component) hne _ y hyK hyL hy3 hyZ
  have hle := h.pRank_barM_normalizer_le Nat.prime_three (by decide)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hrank
  omega

theorem AGLPair.false_of_one_weakSBlock_of_rank (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2) (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ u ∈ E, IsPGroup 3 (Subgroup.zpowers u)) → IsElemAbelian 3 E →
      Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2)
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  set S := pCoreOf 2 H
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set Lb := barM M L
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set Kb := barM M (Subgroup.normalizer (S : Set G))
  have h3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 h3 M
  set Eb := barM M E
  have hrE : Open.pRank 3 M ≤ Open.pRank 3 E :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 h3 E) ⟨E, le_rfl, hE, hEcard⟩
  have hEb : Open.pRank 3 Eb = Open.pRank 3 E := pRank_barM_eq h3 (by decide) M E hEM
  have hEbel : IsElemAbelian 3 Eb := isElemAbelian_barM hE
  have hu3 : ∀ u ∈ Eb, IsPGroup 3 (Subgroup.zpowers u) := fun u hu =>
    isPGroup_zpowers_of_pow_eq_one (hEbel.2 u hu)
  have hEN : Eb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun u hu =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL (hu3 u hu)
  have hR : Open.pRank 3 Eb ≤ Open.pRank 3 (Eb ⊓ Cb) + 2 := hrank Eb hEN hu3 hEbel
  have hFK : Eb ⊓ Cb ≤ Kb := fun u hu =>
    h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2
      fun L' hL' => (hk1 L' hL').symm ▸ hu.2
  obtain ⟨y, hyPL, hy3, hyC⟩ := hy
  have hyK : y ∈ Kb := barM_mono inf_le_left hyPL
  have hyL : y ∈ Lb := barM_mono inf_le_right hyPL
  set Y := Subgroup.zpowers y
  have hYF : Y ⊓ (Eb ⊓ Cb) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz.1
    rw [Subgroup.mem_bot]
    by_contra hne
    apply hyC
    have hk : ¬ (3 : ℤ) ∣ k := by
      intro hdvd
      obtain ⟨m, rfl⟩ := hdvd
      apply hne
      rw [zpow_mul, show y ^ (3 : ℤ) = 1 by exact_mod_cast hy3, one_zpow]
    have hord : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hcop3 : Int.gcd k 3 = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd Int.prime_three).mpr hk).symm
    have hcop : Int.gcd k (orderOf y) = 1 := by
      rcases (Nat.dvd_prime h3).mp hord with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact_mod_cast hcop3
    have hmem : y ∈ Subgroup.zpowers (y ^ k) := mem_zpowers_zpow_iff.mpr hcop
    exact (Subgroup.zpowers_le.mpr hz.2.2) hmem
  have hcomm : ∀ a ∈ Y, ∀ b ∈ Eb ⊓ Cb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hyb : y * b = b * y := Subgroup.mem_centralizer_iff.mp hb.2 y hyL
    exact (Commute.zpow_left hyb k).eq
  have hsum := pRank_add_le_pRank_sup_of_coprime h3 hcomm (by rw [hYF]; simp)
  have hY1 : 1 ≤ Open.pRank 3 Y := by
    have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
    have hYel : IsElemAbelian 3 Y := by
      refine ⟨inferInstance, fun z hz => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show y ^ ((3 : ℕ) : ℤ) = 1 by
        exact_mod_cast hy3, one_zpow]
    have hcard : Nat.card Y = 3 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hy3 hy1
    exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 h3 Y)
      ⟨Y, le_rfl, hYel, hcard⟩
  have hsupK : Y ⊔ (Eb ⊓ Cb) ≤ Kb := sup_le (Subgroup.zpowers_le.mpr hyK) hFK
  have hK2 := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsupK).trans
    (h.pRank_barM_normalizer_le h3 (by decide))
  omega

theorem AGLPair.false_of_one_weakSBlock_of_rankTwo (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2) (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (ho : ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsElemAbelian 3 E →
      Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2)
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False :=
  h.false_of_one_weakSBlock_of_rank h84 h86 hD2 hH hM4 hthree hL hk1
    (fun E hEN hu3 hEbel => hrank E hEN (fun u hu => ho u (hEN hu) (hu3 u hu)) hEbel) hy

theorem one_le_pRank_of_dvd {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    {Y : Subgroup X} (hY : q ∣ Nat.card Y) : 1 ≤ Open.pRank q Y := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hY
  set Z : Subgroup X := Subgroup.zpowers (y : X)
  have hyq : (y : X) ^ q = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hZel : IsElemAbelian q Z := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyq, one_zpow]
  have hcard : Nat.card Z = q ^ 1 := by
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe, hy]
  have hZY : Z ≤ Y := Subgroup.zpowers_le.mpr y.2
  exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove q hq Y)
    ⟨Z, hZY, hZel, hcard⟩

end CFSG.AGLEmbeddingD2
