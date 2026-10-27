module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorFixedOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullIdentification

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v w

variable {G : Type u} [Group G] [Finite G]

theorem original_right_orbit_model_identification_of_odd_kernel
    {F : Type v} [Group F] [Finite F] {Xi : Type w} [MulAction F Xi]
    (H L : Subgroup G) (a : pointRightCosetSpace H)
    (hP : fusionStronglyEmbedded ((rightCosetStabilizer H a).subgroupOf L))
    (f : L →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (hker : f.ker ≤ (rightCosetStabilizer H a).subgroupOf L)
    (hrank : TwoRankAtLeastTwo F) (htrans : MulAction.IsPretransitive F Xi)
    (b : Xi) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b)) :
    letI := numeratorRightOrbitAction H L a
    ∃ (c : MulAut F) (phi : numeratorRightOrbit H L a ≃ Xi),
      ((rightCosetStabilizer H a).subgroupOf L).map (c.toMonoidHom.comp f) =
        MulAction.stabilizer F b ∧
      phi ⟨a, numeratorRightOrbit_base H L a⟩ = b ∧
      ∀ (l : L) (x : numeratorRightOrbit H L a), phi (l • x) = c (f l) • phi x := by
  let := numeratorRightOrbitAction H L a
  let aOrbit : numeratorRightOrbit H L a := ⟨a, numeratorRightOrbit_base H L a⟩
  have hstab : MulAction.stabilizer L aOrbit =
      (rightCosetStabilizer H a).subgroupOf L :=
    numeratorRightOrbitAction_stabilizer H L a aOrbit
  obtain ⟨c, phi, hmap, hbase, hequiv⟩ :=
    strong_embedding_transitive_action_identification_of_odd_kernel
      (numeratorRightOrbitAction_transitive H L a) htrans f hf hodd aOrbit b
      (hstab.symm ▸ hP) (hstab.symm ▸ hker) hrank hB
  exact ⟨c, phi, hstab ▸ hmap, hbase, hequiv⟩

theorem original_full_fixedSet_model_of_central_odd_surjection
    {F : Type v} [Group F] [Finite F] {Xi : Type w} [MulAction F Xi]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hfull : elementFixedSet H u =
      numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1))
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)))
    (f : localInvolutionPointHull z u →* F) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center (localInvolutionPointHull z u))
    (hrank : TwoRankAtLeastTwo F) (htrans : MulAction.IsPretransitive F Xi)
    (b : Xi) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b)) :
    letI := hullFixedSetAction H z u
    ∃ (c : MulAut F) (phi : elementFixedSet H u ≃ Xi),
      (H.subgroupOf (localInvolutionPointHull z u)).map (c.toMonoidHom.comp f) =
        MulAction.stabilizer F b ∧
      (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 → phi y = b) ∧
      ∀ (l : localInvolutionPointHull z u) (y : elementFixedSet H u),
        phi (l • y) = c (f l) • phi y := by
  let := hullFixedSetAction H z u
  let := numeratorRightOrbitAction H (localInvolutionPointHull z u) (rightCosetMk H 1)
  have hPbase : fusionStronglyEmbedded
      ((rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf
        (localInvolutionPointHull z u)) := by
    rw [rightCosetStabilizer_base]
    exact hP
  have hker : f.ker ≤ (rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf
      (localInvolutionPointHull z u) := by
    rw [rightCosetStabilizer_base]
    exact hcentral.trans (original_local_hull_center_le_point h u huz)
  obtain ⟨c, phiOrbit, hmap, hbase, hequiv⟩ :=
    original_right_orbit_model_identification_of_odd_kernel H
      (localInvolutionPointHull z u) (rightCosetMk H 1) hPbase f hf hodd hker
      hrank htrans b hB
  let B := hullFixedSetOrbitEquiv H z u (rightCosetMk H 1) hfull
  let phi := B.trans phiOrbit
  rw [rightCosetStabilizer_base] at hmap
  refine ⟨c, phi, hmap, ?_, ?_⟩
  · intro y hy
    have hpoint : B y =
        ⟨rightCosetMk H 1,
          numeratorRightOrbit_base H (localInvolutionPointHull z u) (rightCosetMk H 1)⟩ :=
      Subtype.ext hy
    change phiOrbit (B y) = b
    rw [hpoint]
    exact hbase
  · intro l y
    change phiOrbit (B (l • y)) = c (f l) • phiOrbit (B y)
    rw [hullFixedSetOrbitEquiv_equivariant H z u (rightCosetMk H 1) hfull]
    exact hequiv l (B y)

theorem original_centralizer_full_fixed_model_and_parameter_of_central_odd_surjection
    {F : Type v} [Group F] [Finite F] {Xi : Type w} [MulAction F Xi]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (f : localInvolutionPointHull z u →* F) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center (localInvolutionPointHull z u))
    (hrank : TwoRankAtLeastTwo F)
    (hdouble : MulAction.IsMultiplyPretransitive F Xi 2)
    (b : Xi) (hB : fusionStronglyEmbedded (MulAction.stabilizer F b))
    (q : ℕ) (hq : 1 ≤ q)
    (hcount : Nat.card {x : F // x ∈ MulAction.stabilizer F b ∧ IsInvolution x} = q - 1) :
    letI := hullFixedSetAction H z u
    elementFixedSet H u =
        numeratorRightOrbit H (localInvolutionPointHull z u) (rightCosetMk H 1) ∧
      q = Nat.card ↥(({1} : Set G) ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G))) ∧
      Nat.card (elementFixedSet H u) = Nat.card Xi ∧
      (∃ (c : MulAut F) (phi : elementFixedSet H u ≃ Xi),
        (H.subgroupOf (localInvolutionPointHull z u)).map (c.toMonoidHom.comp f) =
          MulAction.stabilizer F b ∧
        (∀ y : elementFixedSet H u, y.val = rightCosetMk H 1 → phi y = b) ∧
        ∀ (l : localInvolutionPointHull z u) (y : elementFixedSet H u),
          phi (l • y) = c (f l) • phi y) ∧
      MulAction.IsMultiplyPretransitive (localInvolutionPointHull z u)
        (elementFixedSet H u) 2 := by
  let := hullFixedSetAction H z u
  have hP := h.local_embedding u hu huz hescape
  have hfull := original_central_sylow_local_hull_full_fixed_set h S hzS hzcenter
    u huH hu huz hescape
  have htrans : MulAction.IsPretransitive F Xi := by
    let := hdouble
    exact MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨c, phi, hmap, hbase, hequiv⟩ :=
    original_full_fixedSet_model_of_central_odd_surjection h u huz hfull hP f hf
      hodd hcentral hrank htrans b hB
  let E := c.toMonoidHom.comp f
  have hEker : E.ker = f.ker := MonoidHom.ker_mulEquiv_comp f c
  have hparameter := original_point_parameter_of_central_odd_stabilizer_surjection
    h u huz hP E (c.surjective.comp hf) (hEker.symm ▸ hodd)
      (hEker.symm ▸ hcentral) (MulAction.stabilizer F b) hmap q hq hcount
  refine ⟨hfull, hparameter, Nat.card_congr phi, ⟨c, phi, hmap, hbase, hequiv⟩, ?_⟩
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c0 d hab hcd
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp hdouble
    (phi.injective.ne hab) (phi.injective.ne hcd)
  obtain ⟨l, hl⟩ := (c.surjective.comp hf) g
  change c (f l) = g at hl
  refine ⟨l, phi.injective ?_, phi.injective ?_⟩
  · rw [hequiv, hl]
    exact hga
  · rw [hequiv, hl]
    exact hgb

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
