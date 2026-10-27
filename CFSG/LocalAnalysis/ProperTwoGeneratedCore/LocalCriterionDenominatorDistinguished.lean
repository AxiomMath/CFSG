module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorDistinguishedSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairLinear

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open Matrix CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization Pointwise

variable {G : Type*} [Group G]

def ExactLinearDenominatorIdentification
    (H L : Subgroup G) (v : G)
    (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (K : Type) [Field K] (f : ℕ) : Prop :=
  2 ≤ f ∧ Nat.card K = 2 ^ f ∧
    ∃ (e : L ≃* GLAProj (GLASLGroup (Fin 2) K))
      (phi : elementFixedSet H v ≃ ℙ K (Fin 2 → K)),
      letI := productFixedSetAction H L v hLC
      letI := linearStandardAction K
      ∀ x : L, ∀ p : elementFixedSet H v, phi (x • p) = e x • phi p

def ExactSuzukiDenominatorIdentification
    (H L : Subgroup G) (v : G)
    (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (K : Type) [Field K] (a : ℕ) : Prop :=
  1 ≤ a ∧ Nat.card K = 2 ^ (2 * a + 1) ∧
    ∃ (e : L ≃* GLASzGroup a K)
      (phi : elementFixedSet H v ≃
        {p : ℙ K (Fin 4 → K) // p ∈ suppliedSuzukiOvoidSet a K}),
      letI := productFixedSetAction H L v hLC
      ∀ x : L, ∀ p : elementFixedSet H v,
        (phi (x • p) : ℙ K (Fin 4 → K)) =
          (GeneralLinearGroup.toLin (e x : GL (Fin 4) K)).toLinearEquiv •
            (phi p : ℙ K (Fin 4 → K))

variable [Finite G]

theorem distinguished_original_denominator
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hab : rightCosetMk H 1 ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ H ⊓ rightCosetStabilizer H b)
    (huz : Commute u z) (hunoncentral : u ∉ Subgroup.center G)
    (hthree : DistinguishedThreePointCentralization H (H ⊓ rightCosetStabilizer H b) t)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (H ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (H ⊓ rightCosetStabilizer H b).subtype) = ⊤)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L)
    (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    (hoddCore : oddCore L = ⊥)
    {K : Type} [Field K] [Finite K]
    (hmodel : (∃ f, ExactLinearDenominatorIdentification H L (u * t) hLC K f) ∨
      (∃ a, ExactSuzukiDenominatorIdentification H L (u * t) hLC K a)) :
    let alpha := rightCosetMk H 1
    let D := H ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
      (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
      C.relIndex E = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {alpha, b} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      (∀ f, ExactLinearDenominatorIdentification H L (u * t) hLC K f →
        Nat.card W = Nat.card K + 1) ∧
      (∀ a, ExactSuzukiDenominatorIdentification H L (u * t) hLC K a →
        Nat.card W = Nat.card K - 2 ^ (a + 1) + 1 ∨
          Nat.card W = Nat.card K + 2 ^ (a + 1) + 1) := by
  let alpha := rightCosetMk H 1
  let D := H ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
  let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
  let P : Prop := W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
    (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
    (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
    C.relIndex E = Nat.card W ∧
    (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {alpha, b} ∧
      L ⊓ Subgroup.centralizer ({x} : Set G) = W)
  have hlinear : ∀ f, ExactLinearDenominatorIdentification H L (u * t) hLC K f →
      P ∧ Nat.card W = Nat.card K + 1 := by
    intro f hident
    obtain ⟨hf, hcard, e, phi, hequiv⟩ := hident
    obtain ⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull, horder⟩ :=
      distinguished_original_linear_denominator h b hab t htclass hflip u hu hut huD
        huz hunoncentral hthree hgen L hLC hLnormal htL hclass hoddCore
        f hf hcard e phi hequiv
    exact ⟨⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull⟩, horder⟩
  have hsuzuki : ∀ a, ExactSuzukiDenominatorIdentification H L (u * t) hLC K a →
      P ∧ (Nat.card W = Nat.card K - 2 ^ (a + 1) + 1 ∨
        Nat.card W = Nat.card K + 2 ^ (a + 1) + 1) := by
    intro a hident
    obtain ⟨ha, hcard, e, phi, hequiv⟩ := hident
    obtain ⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull, horder⟩ :=
      distinguished_original_suzuki_denominator h b hab t htclass hflip u hu hut huD
        huz hunoncentral hthree hgen L hLC hLnormal htL hclass hoddCore
        a ha hcard e phi hequiv
    exact ⟨⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull⟩, horder⟩
  have hP : P := by
    rcases hmodel with ⟨f, hf⟩ | ⟨a, ha⟩
    · exact (hlinear f hf).1
    · exact (hsuzuki a ha).1
  obtain ⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull⟩ := hP
  exact ⟨hne, hcyclic, hodd, hinv, hprod, hinter, hindex, hfull,
    fun f hf => (hlinear f hf).2, fun a ha => (hsuzuki a ha).2⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
