module

public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreSignalizer
public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreBridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def ExtremalObstructionExists (G : Type) [Group G] [Finite G] : Prop :=
  D1Global G → TheoremD1 G → ¬ FullCoreLocal G →
    ∃ p ∈ rankThreeSigmaA G, ∃ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D

@[expose] def TransitivityCaseFromSteps (G : Type) [Group G] [Finite G] : Prop :=
  D1Global G → TheoremD1 G → TransitivityReduction G → GL83InvariantTwoSylow G →
    GL83RelativePairExclusion G → TransitivityCase G

@[expose] def PConstrainedOvergroupLe (G : Type) [Group G] [Finite G] : Prop :=
  D1Global G → ∀ {p : ℕ}, p ∈ rankThreeSigmaA G → ∀ {P : Sylow p G} {M D : Subgroup G},
    ExtremalObstruction p P M D → ¬ (P : Subgroup G) ≤ normalizer (D : Set G) →
      ∀ {H : Subgroup G}, (P : Subgroup G) ≤ H → CFSG.ABGLocalTools.IsPConstrained p H → H ≤ M

structure FischerRankFourPending (G : Type) [Group G] [Finite G] : Prop where
  exists_extremal_obstruction : ExtremalObstructionExists G
  transitivityCase : TransitivityCaseFromSteps G
  le_of_isPConstrained : PConstrainedOvergroupLe G

theorem fullCoreLocal_of_transitivityCase (hS : D1Global G) (hD1 : TheoremD1 G)
    (hex : ExtremalObstructionExists G) (hB : TransitivityCase G) : FullCoreLocal G := by
  by_contra hfail
  obtain ⟨p, hp, P, M, D, hext⟩ := hex hS hD1 hfail
  obtain ⟨-, -, -, hDM⟩ := hext.obstruction
  have hpβ := mem_betaFour_of_mem_sigmaA hS.rank hp
  have hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G) :=
    not_le_normalizer_of_four_le hpβ.1 hpβ.2.1 hext (four_le_pRank_sylow hpβ P)
  obtain ⟨hC, T, hT, hNT, htrans⟩ := hB p hp P M D hext hPD
  exact hDM (rankTwo_normalizer_le_of_signalizer_transitivity D M T hT hC hNT htrans)

theorem fullCoreLocality_of_transitivityCase (hS : D1Global G) (hD1 : D1For G)
    (hex : ExtremalObstructionExists G) (hB : TransitivityCase G) : FullCoreLocality G :=
  (fullCoreLocal_iff hS.rank).mp
    (fullCoreLocal_of_transitivityCase hS (theoremD1_of_d1For hS.rank hD1) hex hB)

theorem transitivityReduction_of_layerLemma (hS : D1Global G)
    (hpend : PConstrainedOvergroupLe G) (h23 : GL83LayerLemma G) : TransitivityReduction G := by
  intro p hp P M D hext hPD z hzD hz1 hzc hzp
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained p
      (normalizer ((zpowers z : Subgroup G) : Set G))
  · exact hpend hS hp hext hPD (le_normalizer_zpowers_of_le_centralizer hzc) hcon
  · exact normalizer_zpowers_le_of_layerLemma hS h23 hp hext hPD hzD hz1 hzc hzp hcon

theorem fullCoreLocality_of_pending (hS : D1Global G) (hD1 : D1For G)
    (hpend : FischerRankFourPending G) (h23 : GL83LayerLemma G) (h13 : GL83InvariantTwoSylow G)
    (hX : GL83RelativePairExclusion G) : FullCoreLocality G :=
  fullCoreLocality_of_transitivityCase hS hD1 hpend.exists_extremal_obstruction
    (hpend.transitivityCase hS (theoremD1_of_d1For hS.rank hD1)
      (transitivityReduction_of_layerLemma hS hpend.le_of_isPConstrained h23) h13 hX)

@[expose] def LayerLemmaRank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      GL83LayerLemma G

@[expose] def InvariantTwoSylowOfD1Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      D1For G → TransitivityReduction G → GL83InvariantTwoSylow G

@[expose] def RelativePairExclusionOfD1Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      D1For G → TransitivityReduction G → GL83InvariantTwoSylow G → GL83RelativePairExclusion G

theorem fullCoreRank4_of_pending (hD1 : D1Rank4)
    (hpend : ∀ (G : Type) [Group G] [Finite G], FischerRankFourPending G)
    (h23 : LayerLemmaRank4) (h13 : InvariantTwoSylowOfD1Rank4)
    (hX : RelativePairExclusionOfD1Rank4) : FullCoreRank4 := by
  intro G _ _ _ hnonab hK hchar he hpre
  have hS : D1Global G := ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
  have hD1G : D1For G := hD1 G hnonab hK hchar he hpre
  have hL : GL83LayerLemma G := h23 G hnonab hK hchar he hpre
  have hR : TransitivityReduction G :=
    transitivityReduction_of_layerLemma hS (hpend G).le_of_isPConstrained hL
  have h13G : GL83InvariantTwoSylow G := h13 G hnonab hK hchar he hpre hD1G hR
  exact fullCoreLocality_of_pending hS hD1G (hpend G) hL h13G
    (hX G hnonab hK hchar he hpre hD1G hR h13G)

end CFSG.LocalAnalysis.RankFourTheoremC
