module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduction

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def BlockPLThreeSolv {G : Type} [Group G] (M S L : Subgroup G) : Prop :=
  ∀ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    ⁅Y, Y⁆ = Y → ¬ 3 ∣ Nat.card Y

section Assembly

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

omit [Finite G] in
theorem exists_order_three_noncentral {M S L : Subgroup G} (hLM : L ≤ M)
    (h3L : BlockHasThree M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨y, ⟨hyN, hyL⟩, hy3, l, hl, hyl⟩ := h3L
  set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hLM hyL⟩
  have hybP : yb ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyN, hyL⟩)
  have hybL : yb ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hybC : yb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hc =>
    barM_not_commute hLM hyL hl hyl (Subgroup.mem_centralizer_iff.mp hc _
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl))).symm
  obtain ⟨e, he1, he2⟩ := exists_pow_not_mem_centralizer (isPGroup_zpowers_mk _ hy3) hybC
  set a := yb ^ 3 ^ e
  refine ⟨a, Subgroup.pow_mem _ hybP _, ?_, he1⟩
  have haZ : a ^ 3 ∈ barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    ⟨Subgroup.pow_mem _ (Subgroup.pow_mem _ hybL _) _, he2⟩
  have ha3 : IsPGroup 3 (Subgroup.zpowers (a ^ 3)) := by
    have hmem : a ^ 3 ∈ Subgroup.zpowers yb :=
      (Subgroup.zpowers yb).pow_mem ((Subgroup.zpowers yb).pow_mem (Subgroup.mem_zpowers yb)
        (3 ^ e)) 3
    exact (isPGroup_zpowers_mk (hLM hyL) hy3).to_le (Subgroup.zpowers_le.mpr hmem)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ha3) ⟨a ^ 3, Subgroup.mem_zpowers _⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf (⟨a ^ 3, haZ⟩ : (barM M L ⊓ Subgroup.centralizer
      (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hk] at h1
  have hk0 : k = 0 := by
    by_contra hk0
    exact hZ ((dvd_pow_self 3 hk0).trans h1)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem AGLPair.false_of_two_weakSBlocks_of_center (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2) {L₁ L₂ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hZ₁ : 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hy₁ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy₂ : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  set L₁b := barM M L₁
  set L₂b := barM M L₂
  set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set Kb := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    hL₁.component hL₂.component hne
  have hL₁C₂ : L₁b ≤ C₂ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ₁
  rw [Subgroup.orderOf_mk] at hz
  have hzK : z ∈ Kb := h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2
    fun L' hL' => by
      rcases hk2 L' hL' with he | he
      · exact he.symm ▸ hzZ.2
      · exact he.symm ▸ hL₁C₂ hzZ.1
  obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ := hy₁
  obtain ⟨y₂, hy₂P, hy₂3, hy₂C⟩ := hy₂
  have hy₁K : y₁ ∈ Kb := barM_mono inf_le_left hy₁P
  have hy₂K : y₂ ∈ Kb := barM_mono inf_le_left hy₂P
  have hy₁L : y₁ ∈ L₁b := barM_mono inf_le_right hy₁P
  have hy₂L : y₂ ∈ L₂b := barM_mono inf_le_right hy₂P
  have hrk1 : ∀ w : ↥M ⧸ CFSG.pCore 2 ↥M, w ^ 3 = 1 → w ≠ 1 →
      1 ≤ Open.pRank 3 (Subgroup.zpowers w) := fun w hw3 hw1 =>
    one_le_pRank_of_dvd h3 (by rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1])
  have hdisj : ∀ (w : ↥M ⧸ CFSG.pCore 2 ↥M) (Y : Subgroup _), w ^ 3 = 1 → w ∉ Y →
      Subgroup.zpowers w ⊓ Y = ⊥ := by
    intro w Y hw3 hwY
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu.1
    rw [Subgroup.mem_bot]
    by_contra hne'
    apply hwY
    have hk : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨m, rfl⟩
      apply hne'
      rw [zpow_mul, show w ^ (3 : ℤ) = 1 by exact_mod_cast hw3, one_zpow]
    have hord : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    have hcop3 : Int.gcd k 3 = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd Int.prime_three).mpr hk).symm
    have hcop : Int.gcd k (orderOf w) = 1 := by
      rcases (Nat.dvd_prime h3).mp hord with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact_mod_cast hcop3
    exact (Subgroup.zpowers_le.mpr hu.2) (mem_zpowers_zpow_iff.mpr hcop)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁C (h1 ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h1 => hy₂C (h1 ▸ Subgroup.one_mem _)
  have hcomm1 : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow (Subgroup.mem_centralizer_iff.mp hzZ.2 y₁ hy₁L) i j)).eq
  have hi1 : Subgroup.zpowers y₁ ⊓ Subgroup.zpowers z = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    have h0 := hdisj y₁ C₁ hy₁3 hy₁C
    have : u ∈ Subgroup.zpowers y₁ ⊓ C₁ :=
      ⟨hu.1, (Subgroup.zpowers_le.mpr hzZ.2) hu.2⟩
    rw [h0] at this
    exact this
  have hs1 := pRank_add_le_pRank_sup_of_coprime h3 hcomm1 (by rw [hi1]; simp)
  have hABC₂ : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z ≤ C₂ :=
    sup_le (Subgroup.zpowers_le.mpr (hL₁C₂ hy₁L)) (Subgroup.zpowers_le.mpr (hL₁C₂ hzZ.1))
  have hcomm2 : ∀ a ∈ Subgroup.zpowers y₂,
      ∀ b ∈ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp (hABC₂ hb) y₂ hy₂L) i).eq
  have hi2 : Subgroup.zpowers y₂ ⊓ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z) = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    have h0 := hdisj y₂ C₂ hy₂3 hy₂C
    have : u ∈ Subgroup.zpowers y₂ ⊓ C₂ := ⟨hu.1, hABC₂ hu.2⟩
    rw [h0] at this
    exact this
  have hs2 := pRank_add_le_pRank_sup_of_coprime h3 hcomm2 (by rw [hi2]; simp)
  have hsup : Subgroup.zpowers y₂ ⊔ (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z) ≤ Kb :=
    sup_le (Subgroup.zpowers_le.mpr hy₂K)
      (sup_le (Subgroup.zpowers_le.mpr hy₁K) (Subgroup.zpowers_le.mpr hzK))
  have hK := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsup).trans
    (h.pRank_barM_normalizer_le h3 (by decide))
  have r1 := hrk1 y₁ hy₁3 hy₁1
  have r2 := hrk1 y₂ hy₂3 hy₂1
  have r3 := hrk1 z hz3 hz1
  omega

theorem AGLPair.blockPLThreeSolv_of_perfectThreePrime {G : Type} [Group G] [Finite G]
    {M H R : Subgroup G} (hpair : AGLPair 3 M H R) (hperf : D2PerfectThreePrime H M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    BlockPLThreeSolv M (pCoreOf 2 H) L := by
  intro Y hY hYp hY3
  set T := Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L
  have hTH : T ≤ H := inf_le_left.trans hpair.normalizer_twoCore_H.le
  have hTM : T ≤ M := inf_le_right.trans hL.le
  obtain ⟨n, hn⟩ := exists_iterCommutator_perfect T
  have hD := hperf _ ((iterCommutator_le T n).trans (le_inf hTH hTM)) hn
  have hYD : Y ≤ (iterCommutator (T.subgroupOf M) n).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    rw [iterCommutator_map]
    exact le_iterCommutator_of_commutator_eq hYp hY n
  have hTMn : (iterCommutator (T.subgroupOf M) n).map M.subtype = iterCommutator T n := by
    rw [iterCommutator_map, Subgroup.map_subgroupOf_eq_of_le hTM]
  apply hD
  refine hY3.trans ((Subgroup.card_dvd_of_le hYD).trans ((Subgroup.card_map_dvd _ _).trans ?_))
  rw [← Subgroup.card_map_of_injective M.subtype_injective, hTMn]

theorem d2PairSolv :
    ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
      ∀ (P : Sylow 3 G) (M A H R : Subgroup G), D2Escape 3 P M A H R → D2EscapeMax 3 P M R →
      3 ∈ GLBBetaFour G → AGLPair 3 M H R → GLBStronglyEmbedded 3 M → D2PerfectThreePrime H M →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockPLThreeSolv M (pCoreOf 2 H) L := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ hpair hSE hperf L hL
  exact hpair.blockPLThreeSolv_of_perfectThreePrime hperf hL

end Assembly

end CFSG.AGLEmbeddingD2
