module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.RankCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltTypes

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.McLaughlin

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem three_le_pRank_of_oneImage (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (ho : ClauseO M L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    3 ≤ Open.pRank 3 L := by
  obtain ⟨F, -, -, h1, h2⟩ := rank_count_one_weakSBlock h h84 h86 hD2 hH hM4 hthree hL hk1 ho hZ
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_order_three_noncentral hL.le (hthree L hL) hZ
  have hy1 : y ≠ 1 := fun he => hyC (he ▸ Subgroup.one_mem _)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : 3 ∣ Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
    have := orderOf_dvd_natCard (⟨y, hyP⟩ : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))
    rwa [Subgroup.orderOf_mk, hord] at this
  have h3 := one_le_pRank_three_of_dvd hdvd
  omega

theorem pRank_le_two_of_nineThreeFive {L : Subgroup G} (hLM : L ≤ M) (h5 : NineThreeFive M L) :
    Open.pRank 3 L ≤ 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  have := pRank_barM_le_of_alt e
  rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]
  simpa using this

theorem false_of_oneImage_nineThreeFive (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h5 : NineThreeFive M L) : False := by
  have hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    rw [barM_inf_centralizer_eq_bot_of_alt (by norm_num) e, Subgroup.card_bot]
    norm_num
  have h3 := three_le_pRank_of_oneImage h h84 h86 hD2 hH hM4 hthree hL hk1
    (clauseO_nineThreeFive h5) hZ
  have := pRank_le_two_of_nineThreeFive hL.le h5
  omega

theorem pRank_le_two_of_nineThreeSix {S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h6 : NineThreeSix M S L) (hsolv : BlockPLThreeSolv M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    Open.pRank 3 L ≤ 2 := by
  obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
  have hcop : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (Subgroup.center ↥(barM M L))).ker) := by
    rw [QuotientGroup.ker_mk', ← card_inf_centralizer_eq_card_center] at *
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ
  have h1 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
    (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) (QuotientGroup.mk'_surjective _) hcop
  rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L), h1,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e]
  have := pRank_three_alternating_le (N := 2 * n)
  omega

theorem false_of_oneImage_nineThreeSix (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (h6 : NineThreeSix M (pCoreOf 2 H) L) (hsolv : BlockPLThreeSolv M (pCoreOf 2 H) L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) : False := by
  have h3 := three_le_pRank_of_oneImage h h84 h86 hD2 hH hM4 hthree hL hk1
    (clauseO_nineThreeSix hL h6) hZ
  have := pRank_le_two_of_nineThreeSix hL h6 hsolv hZ
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
