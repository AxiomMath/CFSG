module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Sporadic.Bridge.Converse
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankHNFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicRankFiveB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MonsterD2PRank
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank
public import CFSG.Open.MonsterY443Finiteness

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Blueprint Subgroup

theorem kdSpor_sylow_le_of_not_dvd_index {p : ℕ} [Fact p.Prime] {Z : Type} [Group Z] [Finite Z]
    (K : Subgroup Z) [K.Normal] (hK : ¬ p ∣ K.index) (Q : Sylow p Z) :
    (Q : Subgroup Z) ≤ K := by
  have hQ : IsPGroup p ((Q : Subgroup Z).map (QuotientGroup.mk' K)) :=
    Q.isPGroup'.map _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : Nat.card ((Q : Subgroup Z).map (QuotientGroup.mk' K)) ∣ K.index :=
    Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra h
    exact hK ((dvd_pow_self p h).trans hdvd)
  subst hn0
  rw [pow_zero, Subgroup.card_eq_one] at hn
  intro x hx
  have hmem : (x : Z ⧸ K) ∈ (Q : Subgroup Z).map (QuotientGroup.mk' K) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hn, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).1 hmem

theorem kdSpor_pow_three_dvd_card {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup p Q) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (hab : a * b ≠ b * a) : p ^ 3 ∣ Nat.card Q := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have h3 : 3 ≤ n := by
    by_contra h
    push Not at h
    apply hab
    interval_cases n
    · have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      have hq : a = b := congrArg Subtype.val (Subsingleton.elim (⟨a, ha⟩ : Q) ⟨b, hb⟩)
      rw [hq]
    · have hcard : Nat.card Q = p := by simpa using hn
      haveI : IsCyclic Q := isCyclic_of_prime_card hcard
      letI : CommGroup Q := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Q) ⟨b, hb⟩)
    · have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := Q) hn
      exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  rw [hn]
  exact pow_dvd_pow p h3

theorem kdSpor_sporPair_of_cube {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (s : TauCeti.SporadicName)
    (h : p ^ 3 ∣ CFSG.AGLEmbedding.sporOrd s) :
    (s = .Co1 ∧ p = 5) ∨ (s = .Ly ∧ p = 5) ∨ (s = .HN ∧ p = 5) ∨ (s = .B ∧ p = 5) ∨
      (s = .M ∧ p = 5) ∨ (s = .M ∧ p = 7) ∨ P64SporPairB p s ∨ P64SporPairC p s := by
  rcases CFSG.AGLEmbedding.offList_cases s p hp (by omega) h with h1 | h2
  · unfold CFSG.AGLEmbedding.P1ThreeSporList at h1
    rcases h1 with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
    · omega
    · rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [P64SporPairB, P64SporPairC]
    · rcases hs with rfl | rfl <;> simp [P64SporPairB, P64SporPairC]
    · rcases hs with rfl <;> simp [P64SporPairB, P64SporPairC]
  · unfold CFSG.AGLEmbedding.P1OffRow at h2
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first | omega | simp [P64SporPairB, P64SporPairC]

theorem kdI278Spor_holds
    : KDI278Spor := by
  intro p hp hp5 Z _ _ K hKn s hs hcen hrank Q hQ
  obtain ⟨a, ha, b, hb, -, -, hab⟩ := hQ
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hp2 : p ≠ 2 := by omega
  haveI : K.Normal := hKn
  have hKC : Nonempty (↥K ≃* NativeSporadic.Carrier s) := by
    obtain ⟨eK⟩ := hs
    obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
    exact ⟨eK.trans eC.symm⟩
  obtain ⟨e⟩ := hKC
  haveI hfinC : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  haveI hsimpM : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    (CFSG.Sporadic.Bridge.carrier_M_finite_simple CFSG.Open.Open.monster_y443_derived_card
      CFSG.Open.Open.monster_y443_derived_simple).2
  have hcardK : Nat.card ↥K = CFSG.AGLEmbedding.sporOrd s := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s
  have hC : Subgroup.centralizer (K : Set Z) ≤ K := by
    rw [hcen]
    exact bot_le
  have hnotOut : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
    by_cases hM : s = .M
    · subst hM
      haveI : IsSimpleGroup ↥K := e.isSimpleGroup
      rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
      exact hp.not_dvd_one
    · have hO := CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M s hM
      have hEq : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) =
          Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
            (NativeSporadic.Carrier s)) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
      haveI : Finite (MulAut ↥K) := MulEquiv.finite_left
      have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
        Nat.card_pos
      intro hdvd
      have := Nat.le_of_dvd hpos hdvd
      omega
  have hnotIdx : ¬ p ∣ K.index := fun h =>
    hnotOut (h.trans (CFSG.LargeExtraspecial.S14.index_dvd_card_outer K hC))
  have hQK : (Q : Subgroup Z) ≤ K := kdSpor_sylow_le_of_not_dvd_index K hnotIdx Q
  have hcube : p ^ 3 ∣ CFSG.AGLEmbedding.sporOrd s := by
    rw [← hcardK]
    exact (kdSpor_pow_three_dvd_card (Q : Subgroup Z) Q.isPGroup' ha hb hab).trans
      (Subgroup.card_dvd_of_le hQK)
  have hle : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2 := by
    have := CFSG.SectionRank.pRank_top_le_of_injective hp1 K.subtype K.subtype_injective
    rw [hrank] at this
    exact this
  have hleC : CFSG.Open.pRank p (⊤ : Subgroup (NativeSporadic.Carrier s)) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
    exact hle
  rcases kdSpor_sporPair_of_cube hp hp5 s hcube with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hB | hC'
  ·
    have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_Co1_five
    omega
  ·
    have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_Ly_five
    omega
  ·
    have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_HN_five
    omega
  ·
    have h3 := CFSG.AGLEmbedding.three_le_pRank_B_five
    omega
  ·
    haveI hfinCo1 : Finite (NativeSporadic.Carrier .Co1) :=
      (CFSG.Sporadic.Co1.fam_co1_simplicity).1
    have h3Co1 := CFSG.AGLEmbeddingD2.three_le_pRank_Co1_five
    haveI : IsSimpleGroup ↥K := e.isSimpleGroup
    have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_of_mulEquiv_Carrier_M hp hp2 h3Co1 e
    omega
  ·
    haveI : IsSimpleGroup ↥K := e.isSimpleGroup
    obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
    haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv _ ε.toEquiv
    have h3 := CFSG.AGLEmbedding.Norton.MON5_7.three_le_pRank_seven_gmat
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 7 by norm_num) ε] at hle
    omega
  · exact Or.inl hB
  · exact Or.inr hC'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
