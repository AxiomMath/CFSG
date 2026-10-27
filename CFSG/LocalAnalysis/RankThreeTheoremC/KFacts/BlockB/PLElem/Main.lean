module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.Parabolic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3KFact
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVMain
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers

namespace PLElem

theorem isElemAbelian_of_blockPL_rest (hTPL : CitedBlockTransvectionPL) {G : Type} [Group G]
    [Finite G] {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h : NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L)
    (hsolv : BlockPLThreeSolv M S L) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ blockPL M S L) (hTp : IsPGroup 3 T) : IsElemAbelian 3 T := by
  have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W) := fun W hW hWp =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hsolv W hW hWp)
  have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
  have h72 : ¬ 3 ^ (2 + 1) ∣ (72 : ℕ) := by norm_num
  have hcard : Nat.card T ≤ 3 ^ 2 := by
    have hrest : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
        NineThreeEight M S L → Nat.card T ≤ 3 ^ 2 := fun h' =>
      (card_le_of_not_pow_dvd hT hTp (j := 1)
        (not_nine_dvd_card_blockPL_of_rest hTPL hK hA hL hX hS h' hperf)).trans (by norm_num)
    rcases h with h3 | h4 | h5 | h6 | h7 | h8
    · exact hrest (Or.inl h3)
    · exact card_le_of_not_pow_dvd hT hTp fun hd =>
        h72 (hd.trans (card_blockPL_dvd_of_nineThreeFour h4))
    · obtain ⟨-, ⟨e⟩, -⟩ := h5
      refine card_le_of_not_pow_dvd (hT.trans hPL) hTp fun hd => ?_
      have h2520 : Nat.card (barM M L) = 2520 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      rw [h2520] at hd
      norm_num at hd
    · exact hrest (Or.inr (Or.inl h6))
    · exact hrest (Or.inr (Or.inr (Or.inl h7)))
    · exact hrest (Or.inr (Or.inr (Or.inr h8)))
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_card_le_nine hTp hcard a.2 b.2)⟩⟩,
    fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hTp ⟨x, hx⟩
  exact pow_three_eq_one_of_blockPL_rest hTPL hK hA hL hX hS h hperf (hT hx)
    ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem kFactBlockPLElem_of (hpar : ParabolicThreeElemOfRank)
    (hTPLT : CitedBlockTransvectionPLType) : KFactBlockPLElem := by
  intro G _ _ M S L hK hA _ hL hX hS hconc hsolv hr3 T hT hTp
  rcases hconc with h1 | h2 | hrest
  · exact absurd h1 hX
  · have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M S L → ⁅W, W⁆ = W →
        Nat.Coprime 3 (Nat.card W) := fun W hW hWp =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (hsolv W hW hWp)
    obtain ⟨T₁, hT₁, hN, hne, hperf'⟩ := exists_parabolic_three_of_nineThreeTwo hA hL h2 hS hperf
    have hPL : blockPL M S L ≤ barM M L := barM_mono inf_le_right
    have hrY : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
        pRank_barM_eq Nat.prime_three (by norm_num) M L hL.le]
      exact (CFSG.SectionRank.pRank_mono (by norm_num) hL.le).trans hr3
    exact isElemAbelian_of_subgroupOf hPL
      (hpar _ hL.component.2.2 h2.1 hrY T₁ _ hT₁ hN hne hperf') hT hTp
  · exact isElemAbelian_of_blockPL_rest (citedBlockTransvectionPL_of_type hTPLT) hK hA hL hX hS
      hrest hsolv hT hTp

end PLElem

section Main


theorem kFactBlockPLElem_holds : KFactBlockPLElem :=
  PLElem.kFactBlockPLElem_of
    (PLElem.parabolicThreeElemOfRank_of
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
