module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def LieTwoBigRank (M S L : Subgroup G) : Prop :=
  (NineThreeTwo M S L ∨ NineThreeThree M S L) ∧ 3 ≤ Open.pRank 3 L

@[expose] def BlockCensus (M S L : Subgroup G) : Prop :=
  NineThreeFour M S L ∨
  (Open.pRank 3 L = 2 ∧
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
    (TightRow M L ∨ IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))) ∨
  (NineThreeSeven M S L ∧ (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 12)) ∨
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 16)))) ∨
  Open.pRank 3 L ≤ 1 ∨
  LieTwoBigRank M S L ∨
  (3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
    ¬ NineThreeFour M S L)

theorem blockCensus (hLF : LargeFieldParabolic) (h418 : Agl418) (hL27 : L2SevenRankOne)
    {M S L : Subgroup G} (hL : IsWeakSBlock M S L) (hconc : NineThreeConclusion M S L)
    (hnot1 : ¬ NineThreeOne L)
    (hSyl : NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L) : BlockCensus M S L := by
  by_cases h4 : NineThreeFour M S L
  · exact Or.inl h4
  by_cases hle1 : Open.pRank 3 L ≤ 1
  · exact Or.inr (Or.inr (Or.inr (Or.inl hle1)))
  push Not at hle1
  by_cases hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, h4⟩))))
  have hrq := pRank_top_quot_center_eq hL.le hZ
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hL.le]
  by_cases hr2 : Open.pRank 3 L = 2
  · rcases tightRow_or_L5Two_of_block hLF h418 hL27 hL hconc hnot1 hSyl hsolv hr2 hZ with h | h
    · exact Or.inr (Or.inl ⟨hr2, hZ, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨hr2, hZ, Or.inr h⟩)
  have hr3 : 3 ≤ Open.pRank 3 L := by omega
  rcases hconc with h1 | h2 | h3 | h4' | h5 | h6 | h7 | h8
  · exact absurd h1 hnot1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl h2, hr3⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr h3, hr3⟩))))
  · exact absurd h4' h4
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := id h5
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      hrb
    have hle := pRank_three_alternating_le (N := 7)
    omega
  · exfalso
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      (hrq.trans rfl)
    have hle := pRank_three_alternating_le (N := 2 * n)
    omega
  · obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      hrb
    have hle := pRank_three_alternating_le (N := 4 * n)
    have hn' : n = 3 ∨ n = 4 := by omega
    refine Or.inr (Or.inr (Or.inl ⟨h7, ?_⟩))
    rcases hn' with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  · exact absurd h8 (fun h => not_nineThreeEight h hsolv)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
