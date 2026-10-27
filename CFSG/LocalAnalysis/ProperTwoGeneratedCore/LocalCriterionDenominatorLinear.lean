module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearOrder
import all CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFreeAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open Matrix CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII
open scoped LinearAlgebra.Projectivization Pointwise

section StandardAction

variable (K : Type) [Field K]

@[expose, instance_reducible] def linearStandardAction :
    MulAction (GLAProj (GLASLGroup (Fin 2) K)) (ℙ K (Fin 2 → K)) :=
  MulAction.compHom (ℙ K (Fin 2 → K))
    (glaSLQuotientEquivPSL (ι := Fin 2) (K := K)).toMonoidHom

theorem linearStandardAction_quotient_mk (A : GLASLGroup (Fin 2) K)
    (p : ℙ K (Fin 2 → K)) :
    letI := linearStandardAction K
    (QuotientGroup.mk A : GLAProj (GLASLGroup (Fin 2) K)) • p =
      (GeneralLinearGroup.toLin (A : GL (Fin 2) K)).toLinearEquiv • p := by
  let B : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.toGLKerEquiv.symm A
  have hB : SpecialLinearGroup.toGL B = (A : GL (Fin 2) K) :=
    congrArg Subtype.val (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply A)
  have hquot : glaSLQuotientEquivPSL (QuotientGroup.mk A) =
      (QuotientGroup.mk B : ProjectiveSpecialLinearGroup (Fin 2) K) := by
    apply glaSLQuotientEquivPSL.symm.injective
    rw [MulEquiv.symm_apply_apply]
    simp only [glaSLQuotientEquivPSL, MulEquiv.symm_symm]
    exact congrArg QuotientGroup.mk
      (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply A).symm
  change glaSLQuotientEquivPSL (QuotientGroup.mk A) • p = _
  rw [hquot, ProjectiveSpecialLinearGroup.smul_proj_mk]
  change (GeneralLinearGroup.toLin (SpecialLinearGroup.toGL B)).toLinearEquiv • p = _
  rw [hB]

end StandardAction

variable {G : Type*} [Group G] [Finite G]

theorem original_linear_denominator
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hab : rightCosetMk H 1 ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ H ⊓ rightCosetStabilizer H b)
    (huz : Commute u z) (hunoncentral : u ∉ Subgroup.center G)
    (hthree : ThreePointCentralization H (H ⊓ rightCosetStabilizer H b))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      (oddCore (H ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (H ⊓ rightCosetStabilizer H b).subtype = ⊤)
    (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L)
    (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    (hoddCore : oddCore L = ⊥)
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f)
    (e : L ≃* GLAProj (GLASLGroup (Fin 2) K))
    (phi : elementFixedSet H (u * t) ≃ ℙ K (Fin 2 → K))
    (hequiv : letI := productFixedSetAction H L (u * t) hLC
      letI := linearStandardAction K
      ∀ x : L, ∀ p : elementFixedSet H (u * t), phi (x • p) = e x • phi p) :
    let a := rightCosetMk H 1
    let D := H ⊓ rightCosetStabilizer H b
    let W := L ⊓ D
    let E := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    W ≠ ⊥ ∧ IsCyclic W ∧ Odd (Nat.card W) ∧
      (∀ x ∈ W, rightConjugateElem x t = x⁻¹) ∧
      (E : Set G) = (C : Set G) * (W : Set G) ∧ C ⊓ W = ⊥ ∧
      C.relIndex E = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {a, b} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      Nat.card W = Nat.card K + 1 := by
  have hbase : rightCosetStabilizer H (rightCosetMk H 1) = H :=
    rightCosetStabilizer_base H
  let a := rightCosetMk H 1
  let D := H ⊓ rightCosetStabilizer H b
  let W := L ⊓ D
  have htwo := linear_model_involution_centralizers_two f hf hcard e
  have hSylow := linear_model_oddSylow_cyclic f hf hcard e
  have hcore := actual_denominator_subgroup_conclusions h a b hab t htclass hflip
    u hu hut (hbase.symm ▸ huD) huz hunoncentral (hbase.symm ▸ hthree)
    (hbase.symm ▸ hgen) L hLC hLnormal htL hclass htwo hSylow
  dsimp only at hcore
  rw [hbase] at hcore
  obtain ⟨hWne, hWcyclic, hWodd, _, hinv, hprod, hinter, hindex, hfull, hdisjoint⟩ := hcore
  have hWC : W ≤ Subgroup.centralizer ({u * t} : Set G) := inf_le_left.trans hLC
  have hdiv := denominator_card_dvd_entire_fixedSet H W (u * t) hWC a b
    hdisjoint (fun x hx hne => (hfull x hx hne).1)
  have hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card K + 1 := by
    rw [Nat.card_congr phi]
    exact Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)
  rw [hdegree] at hdiv
  let U := W.subgroupOf L
  let eU : U ≃* W := Subgroup.subgroupOfEquivOfLe (show W ≤ L from inf_le_left)
  have hUcard : Nat.card U = Nat.card W := Nat.card_congr eU.toEquiv
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hWne
    apply Subgroup.card_eq_one.mp
    rw [← hUcard, hU, Subgroup.card_bot]
  have hUcentralizer : ∀ x ∈ U, x ≠ 1 → Subgroup.centralizer ({x} : Set L) = U := by
    intro x hx hxne
    have hxW : (x : G) ∈ W := hx
    have hxGne : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
    have hC : L ⊓ Subgroup.centralizer ({(x : G)} : Set G) = W :=
      (hfull (x : G) hxW hxGne).2
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    change y * x = x * y ↔ (y : G) ∈ W
    rw [← hC]
    constructor
    · intro hy
      exact ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hy)⟩
    · intro hy
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
  have horder := linear_actual_full_centralizer_card f hf hcard e U hUne
    (hUcard.symm ▸ hWodd) (hUcard.symm ▸ hdiv) hUcentralizer
  rw [hUcard] at horder
  have hsupplied_model := And.intro hoddCore hequiv
  clear hsupplied_model
  exact ⟨hWne, hWcyclic, hWodd, hinv, hprod, hinter, hindex, hfull, horder⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
