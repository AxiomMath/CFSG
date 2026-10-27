module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassTripleOrbit
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

universe u

variable {G : Type u} [Group G]

theorem properHull_theta_map_automorphism
    (p : ℕ) (D : Subgroup G) (f : G ≃* G) :
    (minimalLocalFailurePairConfinementTheta p D).map f.toMonoidHom =
      minimalLocalFailurePairConfinementTheta p (D.map f.toMonoidHom) := by
  let e := D.equivMapOfInjective f.toMonoidHom f.injective
  have hcore := CFSG.LocalCores.piCore_map_mulEquiv
    (generatedPairGrowthCanonicalPrimes p) e
  have hmap := congrArg (Subgroup.map (D.map f.toMonoidHom).subtype) hcore
  rw [Subgroup.map_map] at hmap
  change ((CFSG.piCore (generatedPairGrowthCanonicalPrimes p) D).map D.subtype).map
    f.toMonoidHom = _
  rw [Subgroup.map_map]
  have hhom : (D.map f.toMonoidHom).subtype.comp e.toMonoidHom =
      f.toMonoidHom.comp D.subtype := by
    ext x
    rfl
  rwa [hhom] at hmap

theorem properHull_theta_card_right_conjugate (p : ℕ) (D : Subgroup G) (g : G) :
    Nat.card (minimalLocalFailurePairConfinementTheta p (rightConjugate D g)) =
      Nat.card (minimalLocalFailurePairConfinementTheta p D) := by
  change Nat.card (minimalLocalFailurePairConfinementTheta p
    (D.map (MulAut.conj g⁻¹).toMonoidHom)) = _
  rw [← properHull_theta_map_automorphism p D (MulAut.conj g⁻¹)]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem properHull_pair_theta_card_of_transporter
    (H : Subgroup G) (p : ℕ) (alpha beta gamma delta : pointRightCosetSpace H)
    (g : G) (hgamma : pointRightCosetMul H alpha g = gamma)
    (hdelta : pointRightCosetMul H beta g = delta) :
    Nat.card (minimalLocalFailurePairConfinementTheta p
      (rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta)) =
      Nat.card (minimalLocalFailurePairConfinementTheta p
        (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta)) := by
  have hpair : rightConjugate
      (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta) g =
      rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta := by
    change (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta).map
      (MulAut.conj g⁻¹).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    change rightConjugate (rightCosetStabilizer H alpha) g ⊓
      rightConjugate (rightCosetStabilizer H beta) g = _
    rw [properHull_point_stabilizer_right_conjugate,
      properHull_point_stabilizer_right_conjugate, hgamma, hdelta]
  rw [← hpair]
  exact properHull_theta_card_right_conjugate p _ g

theorem properHull_pair_theta_card_of_double_transitivity
    (H : Subgroup G) (p : ℕ)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (alpha beta gamma delta : pointRightCosetSpace H)
    (hab : alpha ≠ beta) (hcd : gamma ≠ delta) :
    Nat.card (minimalLocalFailurePairConfinementTheta p
      (rightCosetStabilizer H gamma ⊓ rightCosetStabilizer H delta)) =
      Nat.card (minimalLocalFailurePairConfinementTheta p
        (rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H beta)) := by
  obtain ⟨g, hac, hbd⟩ := hdoubly alpha beta gamma delta hab hcd
  exact properHull_pair_theta_card_of_transporter H p alpha beta gamma delta g hac hbd

variable [Finite G]

theorem properHull_distinguished_triple_theta_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (r : G) (hr : r ∈ involutionPointClass z)
    (epsilon delta : pointRightCosetSpace H)
    (hfix : pointRightCosetMul H epsilon r = epsilon) (hne : delta ≠ epsilon) :
    Nat.card (minimalLocalFailurePairConfinementTheta p
      ((rightCosetStabilizer H epsilon ⊓ rightCosetStabilizer H delta) ⊓
        rightCosetStabilizer H (pointRightCosetMul H delta r))) =
      Nat.card (minimalLocalFailurePairConfinementTheta p
        (triplePointStabilizer H z beta)) := by
  let : MulAction Gᵐᵒᵖ (pointRightCosetSpace H) := pointRightCosetOppositeMulAction H
  have huniq : ∀ a : pointRightCosetSpace H, rightAct a z = a ↔
      a = rightCosetMk H 1 := by
    intro a
    change pointRightCosetMul H a z = a ↔ a = rightCosetMk H 1
    rw [pointRightCosetMul_eq_translate]
    exact rightCosetTranslate_distinguished_fixed_iff h a
  have hc : ∀ a b : pointRightCosetSpace H,
      a ≠ rightCosetMk H 1 → b ≠ rightCosetMk H 1 →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct a c = b :=
    full_centralizer_transitive_on_original_nonbase_points h S hzS hzcenter hdoubly
  have hzclass : z ∈ involutionPointClass z := distinguished_mem_pointClass z
  have hzfix : rightAct (rightCosetMk H 1) z = rightCosetMk H 1 := (huniq _).mpr rfl
  obtain ⟨g, hag, hbg, _hthird, hconj⟩ := class_triple_transporter z (rightCosetMk H 1)
    huniq hc hzclass hr hzfix hfix hbeta hne
  change pointRightCosetMul H (rightCosetMk H 1) g = epsilon at hag
  change pointRightCosetMul H beta g = delta at hbg
  have htriple := properHull_triple_stabilizer_right_conjugate H z g
    (rightCosetMk H 1) beta
  rw [hag, hbg, hconj] at htriple
  have hbase : ((rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta) ⊓
      rightCosetStabilizer H (pointRightCosetMul H beta z)) = triplePointStabilizer H z beta := by
    rw [pointRightCosetMul_eq_translate]
    rfl
  rw [hbase] at htriple
  rw [← htriple]
  exact properHull_theta_card_right_conjugate p _ g

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
