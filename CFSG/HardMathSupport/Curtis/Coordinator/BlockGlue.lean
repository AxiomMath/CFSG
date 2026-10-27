module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddCentre
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVMain

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem blockPL_le_barM : blockPL M S L ≤ barM M L := barM_mono inf_le_right

theorem blockPL_ne_barM (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) :
    blockPL M S L ≠ barM M L := by
  intro heq
  apply hL.not_le_normalizer
  intro l hl
  have hlM : l ∈ M := hL.le hl
  have hmemL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
    ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [← heq] at hmemL
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈
      barM M (Subgroup.normalizer (S : Set G)) := barM_mono inf_le_left hmemL
  exact coe_mem_of_mk_mem_barM (hA.twoCore_le.trans Subgroup.le_normalizer) ⟨l, hlM⟩ hmem

theorem not_isSylowTwoOf_barM (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hns : ¬ IsSylowTwoOf (S ⊓ L) L) : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun h =>
  hns (isSylowTwoOf_inf_of_barM hL.le hA.twoCore_le hA.twoRadical.isPGroup h)

theorem odd_card_center_barM_of_isWeakSBlock (hL : IsWeakSBlock M S L) :
    Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
  rw [← CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.card_inf_centralizer_eq_card_center]
  exact CFSG.AGLEmbeddingD2.McLaughlin.odd_card_center_barM hL.toIsTwoPrimeComponent

theorem compParab_of_nineThreeTwo (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hns : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    CompParab (barM M L) (blockPL M S L) where
  comp := hL.component
  type := h2.1
  odd := odd_card_center_barM_of_isWeakSBlock hL
  parab := h2.2.1
  ne_top := blockPL_ne_barM hA hL
  ne_borel := ne_inf_normalizer_of_nineThreeTwo h2 (not_isSylowTwoOf_barM hA hL hns)

theorem fixPerfThreeHyp_of_nineThreeTwo (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hns : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hu3 : u ^ 3 = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) :
    FixPerfThreeHyp (barM M L) (blockPL M S L) u where
  parab := compParab_of_nineThreeTwo hA hL hns h2
  perf := fun U hU hUU => coprime_card_blockPL_of_perfect hL hperf U hU hUU
  norm := hu
  pow := hu3
  not_mem := huC
  fix := hfix

end CFSG.HardMathSupport.Curtis.Coordinator
