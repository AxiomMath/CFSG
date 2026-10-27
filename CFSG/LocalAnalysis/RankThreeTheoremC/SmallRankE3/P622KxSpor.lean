module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxEmb
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySetup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSpor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection KFact2401Spor KFactSporLocal
  le_pCoreOf_of_normal commutator_zpowers_le_of_le_normalizer exists_not_commute_of_ne_bot
  exists_isSylowOf_ge normalizer_le_of_stronglyEmbedded_sub)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

namespace P622KxCfg

theorem pCoreOf_inf_facts (c : P622KxCfg p P M x z T S L) :
    pCoreOf 2 (L ⊓ M) ≠ ⊥ ∧ ∃ y ∈ pCoreOf 2 (L ⊓ M), z * y ≠ y * z := by
  have hp := c.prime
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hzM : z ∈ M := c.B_le_M (mem_sup_right (mem_zpowers z))
  set Q₀ : Subgroup G := pCoreOf 2 M ⊓ centralizer ({x} : Set G)
  have hne : ⁅zpowers z, Q₀⁆ ≠ ⊥ :=
    sr629_commutator_pCoreOf_inf_centralizer_ne_bot c.setting c.conf.failure.situation
      c.conf.failure.point c.conf.failure.central
  have hQ₀2 : IsPGroup 2 Q₀ := hO2.to_le inf_le_left
  have hzQ₀ : z ∈ normalizer (Q₀ : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hMO hzM, Subgroup.le_normalizer c.conf.z_mem_centralizer⟩
  have hQ₀L : Q₀ ≤ normalizer (L : Set G) :=
    (le_inf (inf_le_left.trans hOM) inf_le_right).trans c.norm
  obtain ⟨y, hy, hzy⟩ := exists_not_commute_of_ne_bot hp c.ne_two
    c.conf.failure.central.pow_eq_one hQ₀2 hzQ₀ hne
  set U : Subgroup G := ⁅zpowers z, Q₀⁆
  have hUL : U ≤ L := commutator_zpowers_le_of_le_normalizer c.z_mem hQ₀L
  have hUO : U ≤ pCoreOf 2 M := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haM : a ∈ M := (zpowers_le.mpr hzM) ha
    have hbO : b ∈ pCoreOf 2 M := hb.1
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ pCoreOf 2 M := (mem_normalizer_iff.mp (hMO haM) b).mp hbO
    exact (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hbO)
  have hVK : pCoreOf 2 M ⊓ L ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hOM)
  have hKV : L ⊓ M ≤ normalizer ((pCoreOf 2 M ⊓ L : Subgroup G) : Set G) := fun k hk =>
    inf_normalizer_le_normalizer_inf ⟨hMO hk.2, Subgroup.le_normalizer hk.1⟩
  have hV : pCoreOf 2 M ⊓ L ≤ pCoreOf 2 (L ⊓ M) :=
    le_pCoreOf_of_normal hVK hKV (hO2.to_le inf_le_left)
  have hUY : U ≤ pCoreOf 2 (L ⊓ M) := fun u hu => hV ⟨hUO hu, hUL hu⟩
  exact ⟨fun h => hne (le_bot_iff.mp (h ▸ hUY)), y, hUY hy, hzy⟩

theorem normalizer_pCoreOf_inf_eq (c : P622KxCfg p P M x z T S L) :
    normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) ⊓ L = L ⊓ M := by
  have hY2 : IsPGroup 2 (pCoreOf 2 (L ⊓ M)) := pCoreOf_isPGroup 2 (L ⊓ M)
  have hYK : pCoreOf 2 (L ⊓ M) ≤ L ⊓ M := pCoreOf_le 2 (L ⊓ M)
  have hKN : L ⊓ M ≤ normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (L ⊓ M)
  have hzK : z ∈ L ⊓ M := ⟨c.z_mem, c.B_le_M (mem_sup_right (mem_zpowers z))⟩
  have hYne : pCoreOf 2 (L ⊓ M) ⊓ M ≠ ⊥ := by
    rw [inf_eq_left.mpr (hYK.trans inf_le_right)]
    exact c.pCoreOf_inf_facts.1
  have hNM : normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) ≤ M :=
    c.normalizer_le (hYK.trans inf_le_left) hY2 (hKN hzK) hYne
  exact le_antisymm (fun g hg => ⟨hg.2, hNM hg.1⟩) (le_inf hKN inf_le_left)

theorem localRank_three_le (c : P622KxCfg p P M x z T S L) {U : Subgroup G} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) : CFSG.Open.pRank 3 (normalizer (U : Set G) ⊓ L) ≤ 3 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans
    ((local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) (normalizer (U : Set G))
      ⟨U, hU1, hU2, rfl⟩).trans c.setting.rank.le)

theorem le_of_section_three_spor (hL613 : P622L613) (hp3 : p ≠ 3) (h2401 : KFact2401Spor)
    (c : P622KxCfg p P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (h3 : 2 ≤ CFSG.Open.pRank 3 L)
    (hs : s ≠ .M11) {H N : Subgroup G} (hHL : H ≤ L) (hHM : H ≤ M)
    (hsec : S622IsSimpleSection H N) (hzH : z ∈ H) (hzN : z ∉ N) (h3d : 3 ∣ N.relIndex H) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsE : GLBStronglyEmbedded 3 M :=
    c.stronglyEmbedded hL613 hp3 hHL hHM hsec hzH hzN Nat.prime_three (by norm_num) (by omega) h3d
  have h3H : 3 ∣ Nat.card H := h3d.trans (Subgroup.index_dvd_card (N.subgroupOf H))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3H
  have ht3 : IsPGroup 3 (zpowers (t : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
  obtain ⟨E₃, hE₃syl, hXE₃⟩ := exists_isSylowOf_ge (f := 3) (zpowers_le.mpr (hHL t.2)) ht3
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    omega
  have hE₃M : E₃ ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (t : G) ∈ E₃ ⊓ M := ⟨hXE₃ (mem_zpowers _), hHM t.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  have hE₃p : IsPGroup 3 E₃ := hE₃syl.isPGroup
  rcases h2401 G L s e h3 with h | h
  · have hLJ : L ≤ M ⊓ L := h E₃ hE₃syl (M ⊓ L) fun S₀ hS₀E hS₀1 =>
      inf_le_inf_right L (normalizer_le_of_stronglyEmbedded_sub hsE hE₃p hE₃M hS₀E hS₀1)
    exact c.not_le (hLJ.trans inf_le_left)
  · exact absurd h hs

theorem false_of_sporadic_rank3 (hL613 : P622L613) (hp3 : p ≠ 3) (h2401 : KFact2401Spor)
    (hloc : KFactSporLocal) (hOp : rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥)
    (c : P622KxCfg p P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h3 : 2 ≤ CFSG.Open.pRank 3 L) : False := by
  have hp : p.Prime := c.prime
  have hp5 : 5 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have hne4 : p ≠ 4 := by
      intro h4
      rw [h4] at hp
      norm_num at hp
    have hne2 : p ≠ 2 := c.ne_two
    omega
  have hzK : z ∈ L ⊓ M := ⟨c.z_mem, c.B_le_M (mem_sup_right (mem_zpowers z))⟩
  have hclos : ∀ U : Subgroup G, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set G) ⊓ L) ≤ 3 :=
    fun U _ hU1 hU2 => c.localRank_three_le hU1 hU2
  have hclos2 : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → z ∈ normalizer (U : Set G) →
      U ⊓ (L ⊓ M) ≠ ⊥ → normalizer (U : Set G) ⊓ L ≤ L ⊓ M := by
    intro U hUL hU2 hz hUK
    have hUM : U ⊓ M ≠ ⊥ := fun h =>
      hUK (le_bot_iff.mp ((inf_le_inf_left U (inf_le_right : L ⊓ M ≤ M)).trans h.le))
    exact le_inf inf_le_right (inf_le_left.trans (c.normalizer_le hUL hU2 hz hUM))
  obtain ⟨⟨H, N, hHK, hsec, hzH, hzN, h3d⟩, hMs⟩ :=
    hloc G L (L ⊓ M) s z p e h3 hclos hp hp5 c.rank c.orderOf_z inf_le_left hzK
      (fun h => c.not_le (h.trans inf_le_right))
      (le_inf inf_le_right c.normalizer_zpowers_le) hclos2 c.pCoreOf_inf_facts.2
      c.normalizer_pCoreOf_inf_eq
  exact c.le_of_section_three_spor hL613 hp3 h2401 e h3 hMs (hHK.trans inf_le_left)
    (hHK.trans inf_le_right) hsec hzH hzN h3d

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
