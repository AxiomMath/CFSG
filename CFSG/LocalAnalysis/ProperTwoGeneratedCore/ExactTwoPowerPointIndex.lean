module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairStabilizerRankOneHolds
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalPrescribedSylow

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe u

variable {G : Type u} [Group G] [Finite G]

theorem involution_coset_normalizer_exact_two_power_point_index
    (hgen : PairGenerationTheorem G) {H : Subgroup G} {z u : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (T1 : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let U := cosetUnitSet H z u
    let q := Nat.card U
    let k := Nat.card (cosetFixedSet H u)
    let D := pairPointStabilizer H beta
    let T1' := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
    let T := T1' ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
    let Delta := involutionPointClass u ∩ (T : Set G)
    let N := Subgroup.normalizer Delta
    (∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) ∧ 4 ≤ q ∧ (∃ i : ℕ, i ∈ ({1, 2, 3} : Set ℕ) ∧ k = q ^ i + 1) ∧
      Delta = (fun w : G => u * w) '' U ∧ N ≤ H ∧ N ⊓ D = (N ⊓ M) ⊓ D ∧
      (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
      D.relIndex N = q * (k - 1) ∧
      (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
      q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
      (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
        ∀ S : Sylow 2 N, ∃ Q : Sylow 2 G, (Q : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  intro M L U q k D T1' T Delta N
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have hpairRank := ((pairStabilizerRankOneTheorem_of_generation hgen) H z h beta hb).1
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z u ⊓ H)) := inferInstance
  obtain ⟨T₂⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) := inferInstance
  obtain ⟨-, -, hrank, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hb hpairRank huD hu huz hescape R T₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, a, i, ha, hi, -, hq, hq4, hk, -, -, -, hDelta, -,
      hNH, hinter, hQ, hindex, hSylow, hdiv, hglobal⟩ :=
    original_prescribed_sylow_literal_full_index_of_original_rank_data h hcomm hR1 beta hb huD hu
      huz hescape hrank hpairRank.le T1
  exact ⟨⟨a, ha, hq⟩, hq4, ⟨i, hi, hk⟩, hDelta, hNH, hinter, hQ, hindex, hSylow, hdiv, hglobal⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
