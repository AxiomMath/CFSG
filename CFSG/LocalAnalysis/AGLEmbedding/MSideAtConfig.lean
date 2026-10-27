module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1MSideAt (M S : Subgroup G) : Prop where
  isKGroup : Open.IsKGroup ↥M
  glob : CFSG.AGLEmbeddingD2.AGLGlobal G
  maxTwoLocal_M : GLBIsMaxTwoLocal M
  hyp : Asc81bHyp M S
  twoCore_M_le : pCoreOf 2 M ≤ S
  not_le : ¬ S ≤ pCoreOf 2 M

namespace D1MSideAt

variable {M S L : Subgroup G}

theorem le (h : D1MSideAt M S) : S ≤ M := h.hyp.twoRadical.1

theorem isPGroup (h : D1MSideAt M S) : IsPGroup 2 S := by
  rw [h.hyp.twoRadical.2.2]
  exact pCoreOf_isPGroup 2 _

theorem subgroupOf_not_le (h : D1MSideAt M S) : ¬ S.subgroupOf M ≤ CFSG.pCore 2 M := by
  intro hle
  apply h.not_le
  intro x hx
  have hxM : x ∈ M := h.le hx
  have h1 : (⟨x, hxM⟩ : M) ∈ CFSG.pCore 2 ↥M := hle (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : x ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h1, rfl⟩
  assumption

theorem oddCore_le_centralizer (h : D1MSideAt M S) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤ Subgroup.centralizer (barM M S : Set _) :=
  h.hyp.oddCore_le_centralizer h.isKGroup h.maxTwoLocal_M h84 (hD2 G h.glob)

theorem not_isSylowTwoOf_inf (h : D1MSideAt M S) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hL : IsWeakSBlock M S L) : ¬ IsSylowTwoOf (S ⊓ L) L := fun hsyl =>
  hD2 G h.glob M L h.maxTwoLocal_M hL.le hL.subnormal
    (h85 G M S L h.isKGroup h.hyp hL.toIsTwoPrimeComponent hsyl)

theorem exists_weakSBlock (h : D1MSideAt M S) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    ∃ L : Subgroup G, IsWeakSBlock M S L := by
  rcases exists_component_not_le_normalizer_or_not_le_centralizer h.isPGroup.comap_subtype
    h.subgroupOf_not_le with ⟨Lbar, hLbar, hnot⟩ | hodd
  · obtain ⟨L, hL, hbar⟩ := exists_isTwoPrimeComponent hLbar
    refine ⟨L, { toIsTwoPrimeComponent := hL, not_le_normalizer := fun hLS => hnot ?_ }⟩
    rw [← hbar]
    exact barM_le_normalizer_barM hLS
  · exact absurd (h.oddCore_le_centralizer h84 hD2) hodd

theorem nineThree (h : D1MSideAt M S) (h93 : Asc81bNineThree) (hL : IsWeakSBlock M S L) :
    NineThreeConclusion M S L :=
  h93 G M S L h.isKGroup h.hyp hL

theorem nineThree_not_one (h : D1MSideAt M S) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (hL : IsWeakSBlock M S L) :
    ¬ NineThreeOne L ∧ (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) :=
  ⟨fun h1 => hD2 G h.glob M L h.maxTwoLocal_M hL.le hL.subnormal h1, fun _ hsyl =>
    h.not_isSylowTwoOf_inf h85 hD2 hL
      (isSylowTwoOf_inf_of_barM hL.le h.twoCore_M_le h.isPGroup hsyl)⟩

end D1MSideAt

theorem D1PhaseThree.toMSideAt {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) : D1MSideAt M (pCoreOf 2 H) where
  isKGroup := h.isKGroup.1
  glob := h.glob
  maxTwoLocal_M := h.maxTwoLocal_M
  hyp := h.asc81bHyp
  twoCore_M_le := h.twoCore_M_le h.twoCore_inf
  not_le := fun hle => h.twoCore_M_ne (le_antisymm (h.twoCore_M_le h.twoCore_inf) hle)

end CFSG.AGLEmbedding
