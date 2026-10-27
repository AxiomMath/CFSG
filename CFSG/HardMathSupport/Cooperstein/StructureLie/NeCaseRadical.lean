module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Quasithin.SmithC27
open CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem barM_inf_eq_pCoreOf_normalizer (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    barM X (S ⊓ L) = pCoreOf 2 (barM X L ⊓
      Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X))) := by
  have hQ : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hRL : barM X (S ⊓ L) ≤ barM X L := by
    rw [barM_inf hQ]
    exact inf_le_right
  have hRp : IsPGroup 2 (barM X (S ⊓ L)) :=
    isPGroup_barM (hA.twoRadical.isPGroup.to_le inf_le_left)
  apply le_antisymm
  · have hle : barM X (S ⊓ L) ≤ barM X L ⊓
        Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
      le_inf hRL Subgroup.le_normalizer
    exact le_pCoreOf_of_normal_in hle
      (fun h hh a ha => (Subgroup.mem_normalizer_iff.mp hh.2 a).mp ha) hRp
  · set W := pCoreOf 2 (barM X L ⊓
      Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X))) with hWdef
    have hWL : W ≤ barM X L :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_left
    have hWS : W ≤ barM X S := by
      refine le_barM_of_normalizer_le hA hL hWL
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _) ?_
      intro g hg
      have hgR : g ∈ Subgroup.normalizer
          (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
        rw [barM_inf hQ]
        exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1, hg.2⟩
      exact mem_normalizer_pCoreOf (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hg.2, Subgroup.le_normalizer hgR⟩)
    rw [barM_inf hQ]
    exact le_inf hWS hWL

end CFSG.HardMathSupport.Cooperstein.StructureLie
