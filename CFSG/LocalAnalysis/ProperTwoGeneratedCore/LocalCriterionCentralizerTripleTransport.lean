module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportTransitivity

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki.PFAppendixIII
open LocalCriterionCentralizerTripleTransport

theorem centralizer_transitive_triple_sylow_normalizer_action
    {G Ω : Type*} [Group G] [Finite G] [Finite Ω] [MulAction Gᵐᵒᵖ Ω]
    (z : G) (alpha beta : Ω) (hz : IsInvolution z)
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha)
    (hcentralizer : ∀ a b : Ω, a ≠ alpha → b ≠ alpha →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct a c = b)
    (hbeta : beta ≠ alpha) (p : ℕ) (hp : p.Prime)
    (P : Sylow p (tripleStabilizer z alpha beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G)) :
    let U : Subgroup G := (P : Subgroup (tripleStabilizer z alpha beta)).map
      (tripleStabilizer z alpha beta).subtype
    let Delta : Set Ω := rightFixedSet U
    let N := Subgroup.normalizer (U : Set G)
    (alpha ≠ beta ∧ alpha ≠ rightAct beta z ∧ beta ≠ rightAct beta z) ∧
    (alpha ∈ Delta ∧ beta ∈ Delta ∧ rightAct beta z ∈ Delta) ∧
    (∀ n : G, n ∈ N → ∀ a : Ω, a ∈ Delta → rightAct a n ∈ Delta) ∧
    (∀ a b : Ω, a ∈ Delta → b ∈ Delta → a ≠ alpha → b ≠ alpha →
      ∃ n : G, n ∈ N ⊓ rightStabilizer alpha ∧ rightAct a n = b) ∧
    (¬ N ≤ rightStabilizer alpha →
      ∀ a b c d : Ω, a ∈ Delta → b ∈ Delta → c ∈ Delta → d ∈ Delta →
        a ≠ b → c ≠ d →
        ∃ n : G, n ∈ N ∧ rightAct a n = c ∧ rightAct b n = d) := by
  let U : Subgroup G := (P : Subgroup (tripleStabilizer z alpha beta)).map
    (tripleStabilizer z alpha beta).subtype
  let Delta : Set Ω := rightFixedSet U
  let N := Subgroup.normalizer (U : Set G)
  have hthree : alpha ∈ Delta ∧ beta ∈ Delta ∧ rightAct beta z ∈ Delta :=
    triple_subgroup_fixes_three z alpha beta U (Subgroup.map_subtype_le _)
  have hpreserve : ∀ n : G, n ∈ N → ∀ a : Ω, a ∈ Delta → rightAct a n ∈ Delta := by
    intro n hn a ha
    exact normalizer_preserves_rightFixedSet U n hn ha
  have hpoint : ∀ a b : Ω, a ∈ Delta → b ∈ Delta → a ≠ alpha → b ≠ alpha →
      ∃ n : G, n ∈ N ⊓ rightStabilizer alpha ∧ rightAct a n = b :=
    triple_sylow_normalizer_point_stabilizer_transitive hunique hcentralizer hbeta p hp P hzP
  refine ⟨three_points_distinct hz hunique hbeta, hthree, hpreserve, hpoint, ?_⟩
  intro hescape
  exact invariant_set_doubly_transitive_of_point_stabilizer N Delta alpha
    hthree.1 hpreserve hpoint hescape

end CFSG.ProperTwoGeneratedCore
