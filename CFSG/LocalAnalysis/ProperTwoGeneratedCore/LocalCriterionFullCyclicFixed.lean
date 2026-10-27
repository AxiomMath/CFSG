module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_full_cyclic_sylow_fixed_points
    (H Q X : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hswap : rightCosetTranslate H (rightCosetMk H 1) t = beta ∧
      rightCosetTranslate H beta t = rightCosetMk H 1)
    (hXB : X ≤ pairPointStabilizer H beta)
    (hXnormal : (X.subgroupOf (pairPointStabilizer H beta)).Normal)
    (hXcyclic : IsCyclic X)
    (hXcard : Nat.card X = Nat.card (conjugacyWithin H z))
    (hinverts : ∀ x ∈ X, rightConjugateElem x t = x⁻¹)
    (hclass : conjugacyWithin (pairPointStabilizer H beta) t =
      ({t} : Set G) * (X : Set G)) :
    ∀ (p : ℕ), p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
      ∀ A : Sylow p X,
        (∀ A' : Sylow p X, A' = A) ∧
        (A : Subgroup X).Characteristic ∧
        ((cyclicSylowImage X A).subgroupOf (pairPointStabilizer H beta)).Normal ∧
        Nat.card (cyclicSylowImage X A) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p ∧
        (∀ P : Subgroup G, IsPGroup p P → P ≤ pairPointStabilizer H beta →
          cyclicSylowImage X A ≤ P →
          pointFixedSet H P = {rightCosetMk H 1, beta} ∧
          ∃ r ∈ rightPairFlipFiber H z beta,
            r ∈ Subgroup.normalizer (P : Set G) ∧
            Nat.card (conjugacyWithin P r) =
              p ^ (Nat.card (conjugacyWithin H z)).factorization p) ∧
        (∀ y ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer (X : Set G),
          ∀ R : Sylow p
            (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
            cyclicSylowImage X A ≤
              (R : Subgroup
                (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
                (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G)).subtype ∧
            pointFixedSet H
              ((R : Subgroup
                (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
                (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G)).subtype) =
              {rightCosetMk H 1, beta}) := by
  let : IsCyclic X := hXcyclic
  have ht : t ∈ rightPairFlipFiber H z beta := ⟨htclass, hswap.1⟩
  intro p hp hdiv A
  refine ⟨fun A' => cyclic_sylow_unique X hp A' A,
    cyclic_sylow_characteristic X hp A,
    cyclic_sylow_image_normal _ X hXB hXnormal hp A, ?_, ?_, ?_⟩
  · rw [cyclic_sylow_image_card X hp A, hXcard]
  · intro P hP hPB hAP
    exact ⟨containing_cyclic_sylow_whole_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ
      hbeta ht hXcard hinverts hclass p hp hdiv A P hP hPB hAP,
      containing_cyclic_sylow_full_motion h S hzS hzcenter hbeta ht
        hXcard hinverts hclass p hp A P hP hPB hAP⟩
  · intro y hy R
    exact ⟨cyclic_sylow_le_every_centralizer_sylow _ X hXB hXnormal p hp A y hy R,
      centralizer_sylow_whole_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ hbeta ht
        hXB hXnormal hXcard hinverts hclass p hp hdiv A y hy R⟩

end CFSG.ProperTwoGeneratedCore
