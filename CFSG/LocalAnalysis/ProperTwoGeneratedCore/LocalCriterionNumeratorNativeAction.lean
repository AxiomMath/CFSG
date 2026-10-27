module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRecognition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullIdentification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorFixedOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped IsMulCommutative

universe u v

variable {G : Type u} [Group G]

theorem original_right_orbit_image_coset_identification
    {F : Type v} [Group F] (H L : Subgroup G)
    (f : L →* F) (hf : Function.Surjective f) (hker : f.ker ≤ H.subgroupOf L) :
    let B := (H.subgroupOf L).map f
    letI := numeratorRightOrbitAction H L (rightCosetMk H 1)
    ∃ phi : numeratorRightOrbit H L (rightCosetMk H 1) ≃ (F ⧸ B),
      phi ⟨rightCosetMk H 1, numeratorRightOrbit_base H L (rightCosetMk H 1)⟩ =
        QuotientGroup.mk 1 ∧
      ∀ (l : L) (x : numeratorRightOrbit H L (rightCosetMk H 1)),
        phi (l • x) = f l • phi x := by
  let B := (H.subgroupOf L).map f
  let := numeratorRightOrbitAction H L (rightCosetMk H 1)
  let a : numeratorRightOrbit H L (rightCosetMk H 1) :=
    ⟨rightCosetMk H 1, numeratorRightOrbit_base H L (rightCosetMk H 1)⟩
  let b : F ⧸ B := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer L a = H.subgroupOf L := by
    rw [numeratorRightOrbitAction_stabilizer, rightCosetStabilizer_base]
  have hmap : (MulAction.stabilizer L a).map f = MulAction.stabilizer F b := by
    rw [hstab, MulAction.stabilizer_quotient]
  exact transitive_action_equiv_of_surjective_stabilizer_map
    (numeratorRightOrbitAction_transitive H L (rightCosetMk H 1))
    (MulAction.isPretransitive_quotient F B) f hf a b (hstab.symm ▸ hker) hmap

theorem original_full_fixedSet_image_coset_identification
    {F : Type v} [Group F] (H : Subgroup G) (z u : G)
    (hfull : elementFixedSet H u =
      numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1))
    (f : localInvolutionPointHull z u →* F) (hf : Function.Surjective f)
    (hker : f.ker ≤ H.subgroupOf (localInvolutionPointHull z u)) :
    let B := (H.subgroupOf (localInvolutionPointHull z u)).map f
    letI := hullFixedSetAction H z u
    ∃ phi : elementFixedSet H u ≃ (F ⧸ B),
      (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 →
        phi y = QuotientGroup.mk 1) ∧
      ∀ (l : localInvolutionPointHull z u) (y : elementFixedSet H u),
        phi (l • y) = f l • phi y := by
  let := hullFixedSetAction H z u
  let := numeratorRightOrbitAction H (localInvolutionPointHull z u) (rightCosetMk H 1)
  obtain ⟨phiOrbit, hbase, hequiv⟩ := original_right_orbit_image_coset_identification
    H (localInvolutionPointHull z u) f hf hker
  let e := hullFixedSetOrbitEquiv H z u (rightCosetMk H 1) hfull
  let phi := e.trans phiOrbit
  refine ⟨phi, ?_, ?_⟩
  · intro y hy
    have hpoint : e y =
        ⟨rightCosetMk H 1,
          numeratorRightOrbit_base H (localInvolutionPointHull z u) (rightCosetMk H 1)⟩ :=
      Subtype.ext hy
    change phiOrbit (e y) = QuotientGroup.mk 1
    rw [hpoint]
    exact hbase
  · intro l y
    change phiOrbit (e (l • y)) = f l • phiOrbit (e y)
    rw [hullFixedSetOrbitEquiv_equivariant H z u (rightCosetMk H 1) hfull]
    exact hequiv l (e y)

variable [Finite G]

theorem original_central_sylow_native_fixedSet_model
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    let f := QuotientGroup.mk' (CFSG.oddCore L)
    let B := (H.subgroupOf L).map f
    let U := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
    letI := hullFixedSetAction H z u
    IsSimpleBenderGroup F ∧ CFSG.oddCore L ≤ H.subgroupOf L ∧ IsBorelSubgroup B ∧
      elementFixedSet H u = numeratorRightOrbit H L (rightCosetMk H 1) ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧
        IsElementaryAbelian 2 U ∧ U ≤ B ∧
        (U : Set F) = {1} ∪ {x : F | x ∈ B ∧ IsInvolution x} ∧
        Nat.card U = 2 ^ a ∧ 4 ≤ Nat.card U ∧ B.index = (2 ^ a) ^ i + 1 ∧
        Nat.card (elementFixedSet H u) = (2 ^ a) ^ i + 1 ∧
        (∃ phi : elementFixedSet H u ≃ (F ⧸ B),
          (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 →
            phi y = QuotientGroup.mk 1) ∧
          ∀ (l : L) (y : elementFixedSet H u), phi (l • y) = f l • phi y) ∧
        MulAction.IsMultiplyPretransitive L (elementFixedSet H u) 2 := by
  let L := localInvolutionPointHull z u
  let F := L ⧸ CFSG.oddCore L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := (H.subgroupOf L).map f
  let U := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
  let := hullFixedSetAction H z u
  obtain ⟨hmodel, hcore, hB⟩ :=
    original_local_hull_native_model_and_borel h u hu huz hescape hrank
  have hfull := original_central_sylow_local_hull_full_fixed_set h S hzS hzcenter
    u huH hu huz hescape
  have hker : f.ker ≤ H.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact hcore
  obtain ⟨phi, hbase, hequiv⟩ := original_full_fixedSet_image_coset_identification
    H z u hfull f (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hker
  obtain ⟨a, ha, hmodelAt⟩ := hmodel.exists_exponent
  obtain ⟨i, hi, helem, hUB, hUset, hUcard, hfour, hindex⟩ :=
    native_borel_whole_elementary_root_at_exponent a ha hmodelAt hmodel B hB
  have hdouble : MulAction.IsMultiplyPretransitive F (F ⧸ B) 2 :=
    simpleBender_borel_coset_twoTransitive hB hmodel
  have hcard : Nat.card (elementFixedSet H u) = (2 ^ a) ^ i + 1 :=
    (Nat.card_congr phi).trans hindex
  refine ⟨hmodel, hcore, hB, hfull, a, i, ha, hi, hmodelAt, helem, hUB,
    hUset, hUcard, hfour, hindex, hcard, ⟨phi, hbase, hequiv⟩, ?_⟩
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y x' y' hxy hxy'
  obtain ⟨g, hgx, hgy⟩ := MulAction.is_two_pretransitive_iff.mp hdouble
    (phi.injective.ne hxy) (phi.injective.ne hxy')
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore L) g
  refine ⟨l, phi.injective ?_, phi.injective ?_⟩
  · rw [hequiv, hl]
    exact hgx
  · rw [hequiv, hl]
    exact hgy

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
