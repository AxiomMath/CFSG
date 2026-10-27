module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixedAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixedOddCentral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixedParity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem maximal_odd_prime_class_normalizer_has_fixed_point
    {H P : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hthree : 3 ≤ Nat.card (pointFixedSet H P))
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q →
      3 ≤ Nat.card (pointFixedSet H Q) → Q ≤ P)
    (hs : s ∈ involutionPointClass z)
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) :
    ∃ gamma ∈ pointFixedSet H P, pointRightCosetMul H gamma s = gamma := by
  classical
  by_contra hnot
  have hno : ∀ gamma ∈ pointFixedSet H P, pointRightCosetMul H gamma s ≠ gamma := by
    intro gamma hgamma hf
    exact hnot ⟨gamma, hgamma, hf⟩
  let N := Subgroup.normalizer (P : Set G)
  let sN : N := ⟨s, hsP⟩
  let Delta := pointFixedSet H P
  let := pointInvariantSetInverseRightAction H N Delta
    (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
  have htwo : MulAction.IsMultiplyPretransitive N Delta 2 :=
    maximal_three_point_normalizer_two_pretransitive H hdoubly p hp P hP hthree hmax
  have hsOrder : orderOf sN = 2 := (Subgroup.orderOf_coe sN).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order hs)
  have hcentral : QuotientGroup.mk' (CFSG.oddCore N) sN ∈
      Subgroup.center (N ⧸ CFSG.oddCore N) :=
    (no_fixed_point_odd_normalizer_full_class h p hp hodd hP hs hsP hno).2.1
  have hsNo : ∀ a : Delta, sN • a ≠ a := by
    intro a hf
    have hh := congrArg Subtype.val hf
    change pointRightCosetMul H a.val s⁻¹ = a.val at hh
    rw [inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass h.distinguished_order hs)] at hh
    exact hno a.val a.property hh
  have hdegree : Nat.card Delta ≤ 2 :=
    two_pretransitive_odd_central_fixed_free_card_le_two htwo (CFSG.oddCore N)
      (CFSG.ComponentClassification.OddCore.odd_card N) sN hsOrder hcentral hsNo
  change Nat.card (pointFixedSet H P) ≤ 2 at hdegree
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_maximal_odd_prime_fixed_set_normalizing_involution
    {H P : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    (hthree : 3 ≤ Nat.card (pointFixedSet H P))
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q →
      3 ≤ Nat.card (pointFixedSet H Q) → Q ≤ P)
    (hs : s ∈ involutionPointClass z)
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) :
    (∃ gamma ∈ pointFixedSet H P,
      pointRightCosetMul H gamma s = gamma ∧
        ∀ omega : pointRightCosetSpace H, pointRightCosetMul H omega s = omega →
          omega = gamma) ∧
      (∀ gamma : pointRightCosetSpace H, pointRightCosetMul H gamma s = gamma →
        gamma ∈ pointFixedSet H P) ∧
      Odd (Nat.card (pointFixedSet H P)) := by
  obtain ⟨gamma, hgamma, hfixed⟩ := maximal_odd_prime_class_normalizer_has_fixed_point
    h hdoubly p hp hodd hP hthree hmax hs hsP
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨a, _, ha⟩ := huniq s hs
  have hall : ∀ omega : pointRightCosetSpace H,
      pointRightCosetMul H omega s = omega → omega = gamma := by
    intro omega homega
    exact (ha omega homega).trans (ha gamma hfixed).symm
  refine ⟨⟨gamma, hgamma, hfixed, hall⟩, ?_, ?_⟩
  · intro omega homega
    exact hall omega homega ▸ hgamma
  · let N := Subgroup.normalizer (P : Set G)
    let sN : N := ⟨s, hsP⟩
    let Delta := pointFixedSet H P
    let := pointInvariantSetInverseRightAction H N Delta
      (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
    have hsOrder : orderOf sN = 2 := (Subgroup.orderOf_coe sN).symm.trans
      (order_two_of_mem_pointClass h.distinguished_order hs)
    let gammaD : Delta := ⟨gamma, hgamma⟩
    apply involution_unique_fixed_point_card_odd sN hsOrder gammaD
    intro omega
    constructor
    · intro hf
      apply Subtype.ext
      apply hall
      have hh := congrArg Subtype.val hf
      change pointRightCosetMul H omega.val s⁻¹ = omega.val at hh
      rwa [inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass h.distinguished_order hs)] at hh
    · intro heq
      rw [heq]
      apply Subtype.ext
      change pointRightCosetMul H gamma s⁻¹ = gamma
      rwa [inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass h.distinguished_order hs)]

end CFSG.ProperTwoGeneratedCore
