module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalClasses

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

@[expose] def rankTwoCentralizerOrbitData (H : Subgroup G) (z u : G) : Prop :=
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  conjugacyWithin L u = {u} ∧
    conjugacyWithin L z = {x : G | x ∈ L ∧ orderOf x = 2} ∧
    conjugacyWithin L (u * z) =
      (fun x : G => u * x) '' {x : G | x ∈ L ∧ orderOf x = 2} ∧
    {x : G | x ∈ M ∧ orderOf x = 2} =
      conjugacyWithin L u ∪ conjugacyWithin L z ∪ conjugacyWithin L (u * z) ∧
    Disjoint (conjugacyWithin L u) (conjugacyWithin L z) ∧
    Disjoint (conjugacyWithin L u) (conjugacyWithin L (u * z)) ∧
    Disjoint (conjugacyWithin L z) (conjugacyWithin L (u * z)) ∧
    ((U : Set G) \ {1} ⊆ involutionPointClass z) ∧
    ((fun x : G => u * x) '' ((U : Set G) \ {1}) ⊆ involutionPointClass (u * z)) ∧
    (let _ : MulAction L G := MulAction.compHom G
        (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
      ∃ p : SubMulAction L G,
        (p : Set G) = {x : G | x ∈ M ∧ orderOf x = 2} ∧
        ∃ a b c : p,
          (a : G) = u ∧ (b : G) = z ∧ (c : G) = u * z ∧
          Subtype.val '' MulAction.orbit L a = conjugacyWithin L u ∧
          Subtype.val '' MulAction.orbit L b = conjugacyWithin L z ∧
          Subtype.val '' MulAction.orbit L c = conjugacyWithin L (u * z) ∧
          (∀ x : p, x ∈ MulAction.orbit L a ∨
            x ∈ MulAction.orbit L b ∨ x ∈ MulAction.orbit L c) ∧
          Set.range (fun q : MulAction.orbitRel.Quotient L p =>
            Subtype.val '' q.orbit) =
              {conjugacyWithin L u, conjugacyWithin L z, conjugacyWithin L (u * z)} ∧
          Nat.card (MulAction.orbitRel.Quotient L p) = 3) ∧
    ∀ T1 : Sylow 2 ↥(H ⊓ M),
      let A := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
      let T := A ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
      conjugacyWithin L u ∩ (A : Set G) = {u} ∧
      conjugacyWithin L z ∩ (A : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (A : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
      conjugacyWithin L u ∩ (T : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
      let N := L ⊓ Subgroup.normalizer (U : Set G)
      let _ : MulAction N G := MulAction.compHom G
        (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
      ∀ B : Subgroup G, B = A ∨ B = T →
        ∃ p : SubMulAction N G,
          (p : Set G) = {x : G | x ∈ B ∧ orderOf x = 2} ∧
          ∃ a b c : p,
            (a : G) = u ∧ (b : G) = z ∧ (c : G) = u * z ∧
            Subtype.val '' MulAction.orbit N a = {u} ∧
            Subtype.val '' MulAction.orbit N b = (U : Set G) \ {1} ∧
            Subtype.val '' MulAction.orbit N c =
              (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
            (∀ x : p, x ∈ MulAction.orbit N a ∨
              x ∈ MulAction.orbit N b ∨ x ∈ MulAction.orbit N c) ∧
            Disjoint ({u} : Set G) ((U : Set G) \ {1}) ∧
            Disjoint ({u} : Set G)
              ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
            Disjoint ((U : Set G) \ {1})
              ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
            Set.range (fun q : MulAction.orbitRel.Quotient N p =>
              Subtype.val '' q.orbit) =
                {({u} : Set G), (U : Set G) \ {1},
                  (fun x : G => u * x) '' ((U : Set G) \ {1})} ∧
            Nat.card (MulAction.orbitRel.Quotient N p) = 3

variable [Finite G]

theorem original_rank_two_centralizer_orbit_data
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    rankTwoCentralizerOrbitData H z u := by
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 u hu huz hescape hrank
  obtain ⟨hCu, hCz, hCuz, hInv, hd1, hd2, hd3⟩ :=
    original_minimal_failure_entire_centralizer_three_hull_classes
      h beta hbeta hpairRank.le u huD hu huz hescape hrank
  have hglobal := original_minimal_failure_whole_root_global_class_inclusions
    h u hu huz hescape hrank hcentral
  have hclasses := every_original_point_sylow_and_intersection_class_intersections
    h u (pairPointStabilizer_le_point H beta huD) hu huz hescape hrank hcentral
  have hnormalizer := every_original_point_sylow_and_intersection_three_orbits
    h beta hbeta hpairRank.le u huD hu huz hescape hrank hcentral
  have hhullOrbits := original_minimal_failure_entire_centralizer_three_conjugation_orbits
    h beta hbeta hpairRank.le u huD hu huz hescape hrank
  unfold rankTwoCentralizerOrbitData
  simp only [order_two_iff_isInvolution]
  refine ⟨hCu, hCz, hCuz, hInv, hd1, hd2, hd3, hglobal.1, hglobal.2,
    hhullOrbits, ?_⟩
  intro T1
  obtain ⟨hAu, hAz, hAuz, hTu, hTz, hTuz⟩ := hclasses T1
  exact ⟨hAu, hAz, hAuz, hTu, hTz, hTuz, hnormalizer T1⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
