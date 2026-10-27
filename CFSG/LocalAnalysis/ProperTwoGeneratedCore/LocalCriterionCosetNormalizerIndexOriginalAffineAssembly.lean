module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonical

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

universe v

variable {G : Type v} [Group G] [Finite G]

@[expose] def entireAffineNormalizerData (U : Subgroup G) (u : G)
    (K : Subgroup G) (Delta : Set G) : Prop :=
  let N := Subgroup.normalizer Delta
  K ≤ Subgroup.centralizer Delta ∧
    ∃ f : N →* unitAffineGroup U,
      (∀ (n : N) (x : U),
        ((unitAffinePerm U (f n) x : U) : G) =
          u⁻¹ * ((n : G) * (u * (x : G)) * (n : G)⁻¹)) ∧
      f.ker = (Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (U : Set G)).subgroupOf N ∧
      f.ker.map N.subtype = Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (U : Set G) ∧
      K.subgroupOf N ≤ f.ker ∧
      (Subgroup.centralizer Delta).relIndex N = Nat.card f.range ∧
      Nonempty (N ⧸ f.ker ≃* f.range) ∧
      (letI := unitAffineAction U; MulAction.IsMultiplyPretransitive f.range U 2)

@[expose] def originalExactIndexWithNativeAffineData
    (H : Subgroup G) (z u : G) (beta : pointRightCosetSpace H)
    (T1 : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) : Prop :=
  rankTwoCentralizerHullInvolutionsAndLocalOrbits H z u ∧
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let P := L ⊓ H
  let U := originalPointRoot H z u
  let q := Nat.card (cosetUnitSet H z u)
  let Gamma := cosetFixedSet H u
  let k := Nat.card Gamma
  let D := pairPointStabilizer H beta
  let K := M ⊓ Subgroup.centralizer (L : Set G)
  let T1' := (T1 : Subgroup ↥(M ⊓ H)).map (M ⊓ H).subtype
  let T := T1' ⊓ (L ⊔ K)
  let Delta := involutionPointClass u ∩ (T : Set G)
  let N := Subgroup.normalizer Delta
  let R := CFSG.oddCore L
  let F := L ⧸ R
  let B := (H.subgroupOf L).map (QuotientGroup.mk' R)
  properOddCore M ≤ H ∧ ⁅properOddCore M, L⁆ = ⊥ ∧
    properOddCore L ≤ properOddCore M ∧ R ≤ Subgroup.center L ∧ Odd (Nat.card R) ∧
    u * z ∈ involutionPointClass u ∧ L ≤ M ∧ P = L ⊓ H ∧
    IsSimpleBenderGroup F ∧ IsBorelSubgroup B ∧ R ≤ H.subgroupOf L ∧
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      IsSimpleBenderGroupAtExponent a F ∧ q = 2 ^ a ∧ 4 ≤ q ∧ k = q ^ i + 1 ∧
      IsElementaryAbelian 2 U ∧ U ≤ H ⊓ L ∧ (U : Set G) = cosetUnitSet H z u ∧
      Delta = (fun w : G => u * w) '' (U : Set G) ∧
      Delta ∩ (D : Set G) = {u} ∧ N ≤ H ∧
      N ⊓ D = (N ⊓ M) ⊓ D ∧
      (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧
      D.relIndex N = q * (k - 1) ∧
      (∀ S : Sylow 2 N, D.relIndex ((S : Subgroup N).map N.subtype) = q * (k - 1)) ∧
      q * (k - 1) ∣ Nat.card (pointRightCosetSpace H) - 1 ∧
      (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
        ∀ S : Sylow 2 N, ∃ Q : Sylow 2 G,
          (Q : Subgroup G) = (S : Subgroup N).map N.subtype) ∧
      entireAffineNormalizerData U u K Delta

theorem original_exact_index_native_affine_of_original_rank_data
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u))
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (T1 : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    originalExactIndexWithNativeAffineData H z u beta T1 := by
  have hgeometry := unique_rank_two_centralizer_hull_involutions_and_local_orbits
    h hcomm hsmallerR1 beta hb hpairRank u huD hu huz hescape hrank
  obtain ⟨hR, hRL, hLR, hcentral, hodd, hfused, hLM, hP, hmodel, hB, hcore,
      a, i, ha, hi, hAt, hq, hqfour, hk, helem, hUle, hUset, hDelta,
      hsingle, hNH, hinter, hQ, hindex, hSylow, hdiv, hglobal⟩ :=
    original_prescribed_sylow_literal_full_index_of_original_rank_data
      h hcomm hsmallerR1 beta hb huD hu huz hescape hrank hpairRank.le T1
  have hconjugation := original_prescribed_sylow_full_conjugation_of_original_rank_data
    h hcomm hsmallerR1 beta hb huD hu huz hescape hrank hpairRank.le T1
  dsimp only at hconjugation
  have hconj := hconjugation.2
  rw [hDelta, ← hUset] at hconj
  have hu2 : u * u = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu).1
  let U := originalPointRoot H z u
  let hc := originalPointRoot_entire_commutes_u H z u
  have hDeltaroot : involutionPointClass u ∩
      (((T1 : Subgroup ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)).map
        (Subgroup.centralizer ({u} : Set G) ⊓ H).subtype ⊓
          (localInvolutionPointHull z u ⊔
            (Subgroup.centralizer ({u} : Set G) ⊓
              Subgroup.centralizer (localInvolutionPointHull z u : Set G))) : Subgroup G) : Set G) =
      (fun x : G => u * x) '' (U : Set G) := by
    rw [hDelta, hUset]
  unfold originalExactIndexWithNativeAffineData
  refine ⟨hgeometry, ?_⟩
  dsimp only
  refine ⟨hR, hRL, hLR, hcentral, hodd, hfused, hLM, hP, hmodel, hB, hcore,
    a, i, ha, hi, hAt, hq, hqfour, hk, helem, hUle, hUset, hDeltaroot,
    hsingle, hNH, hinter, hQ, hindex, hSylow, hdiv, hglobal, ?_⟩
  rw [hDeltaroot]
  unfold entireAffineNormalizerData
  dsimp only
  refine ⟨original_entire_hull_centralizer_le_entire_coset_centralizer H z u,
    unitAffineHom U u hu2 hc, ?_, unitAffineHom_ker U u hu2 hc,
    unitAffineHom_ker_map U u hu2 hc,
    original_entire_hull_centralizer_le_affine_kernel H z u hu2,
    entire_coset_centralizer_index_eq_affine_image_card U u hu2 hc,
    ⟨unitAffineQuotientEquivRange U u hu2 hc⟩, ?_⟩
  · intro n x
    rw [unitAffineHom_action]
    exact unitCoordinatePerm_apply U u n x
  · exact unitAffineHom_range_isTwoPretransitive U u hu2 hc hconj.1 hconj.2

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
