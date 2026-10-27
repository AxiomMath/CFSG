module

public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtConfig
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1MSideAt

variable {M S L : Subgroup G}

theorem barM_ne_of_isWeakSBlock (h : D1MSideAt M S) (hL : IsWeakSBlock M S L) :
    barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠ barM M L := by
  intro heq
  apply hL.not_le_normalizer
  intro l hl
  have hlM : l ∈ M := hL.le hl
  have hmemL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
    ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [← heq] at hmemL
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈
      barM M (Subgroup.normalizer (S : Set G)) := barM_mono inf_le_left hmemL
  exact coe_mem_of_mk_mem_barM (h.twoCore_M_le.trans Subgroup.le_normalizer) ⟨l, hlM⟩ hmem

theorem blockInnerNormalizer (h : D1MSideAt M S) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hL : IsWeakSBlock M S L) :
    ∀ l ∈ barM M L,
      (∀ s ∈ barM M S, ∃ s' ∈ barM M S, ∀ y ∈ barM M L,
        (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
      l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) :=
  h.hyp.blockInnerNormalizer h.isKGroup h.maxTwoLocal_M h.twoCore_M_le h84 h86 (hD2 G h.glob) hL

end D1MSideAt

end CFSG.AGLEmbedding
