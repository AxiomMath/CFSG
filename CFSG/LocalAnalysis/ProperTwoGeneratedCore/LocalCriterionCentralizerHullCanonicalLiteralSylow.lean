module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe v

variable {G : Type v} [Group G]

theorem original_subgroup_omega_one_literal_inclusion
    (C : Subgroup G) (V : Subgroup C) :
    let A := V.map C.subtype
    (CFSG.omega₁ (G := V) (p := 2)).map (C.subtype.comp V.subtype) =
      (CFSG.omega₁ (G := A) (p := 2)).map A.subtype := by
  let A := V.map C.subtype
  let e : V ≃* A := V.equivMapOfInjective C.subtype C.subtype_injective
  change (CFSG.omega₁ (G := V) (p := 2)).map
      (A.subtype.comp e.toMonoidHom) = _
  rw [← Subgroup.map_map, CFSG.omega₁_map_eq_of_mulEquiv]

@[expose] def rankTwoCentralizerLiteralSylowData (H : Subgroup G) (z u : G) : Prop :=
  let M := Subgroup.centralizer ({u} : Set G)
  let U := originalPointRoot H z u
  ∀ T1 : Sylow 2 ↥(H ⊓ M),
    let f := (H ⊓ M).subtype.comp (T1 : Subgroup ↥(H ⊓ M)).subtype
    (CFSG.omega₁ (G := T1) (p := 2)).map f = Subgroup.zpowers u ⊔ U ∧
    CFSG.omega₁ (G := T1) (p := 2) = (Subgroup.zpowers u ⊔ U).comap f ∧
    f '' {x : T1 | orderOf x = 2} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
    (∃ e : Subgroup.zpowers u × U ≃* CFSG.omega₁ (G := T1) (p := 2),
      ∀ (a : Subgroup.zpowers u) (b : U), f (e (a, b)) = (a : G) * b)

variable [Finite G]

theorem original_rank_two_centralizer_literal_sylow_data
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
    rankTwoCentralizerLiteralSylowData H z u := by
  let M := Subgroup.centralizer ({u} : Set G)
  let C := H ⊓ M
  let U := originalPointRoot H z u
  have hdata := original_rank_two_centralizer_sylow_data
    h hcomm hsmallerR1 beta hbeta hpairRank u huD hu huz hescape hrank
  unfold rankTwoCentralizerLiteralSylowData
  dsimp only
  intro T1
  let V : Subgroup C := T1
  let A := V.map C.subtype
  let f := C.subtype.comp V.subtype
  have hf : Function.Injective f := C.subtype_injective.comp V.subtype_injective
  have hOm := (hdata T1).2.2.1
  have hMap : (CFSG.omega₁ (G := V) (p := 2)).map f = Subgroup.zpowers u ⊔ U :=
    (original_subgroup_omega_one_literal_inclusion C V).trans hOm
  have hPre : CFSG.omega₁ (G := V) (p := 2) = (Subgroup.zpowers u ⊔ U).comap f := by
    rw [← hMap]
    exact (Subgroup.comap_map_eq_self
      (show f.ker ≤ CFSG.omega₁ (G := V) (p := 2) from
        ((MonoidHom.ker_eq_bot_iff f).mpr hf) ▸ bot_le)).symm
  have hInv : f '' {x : V | orderOf x = 2} = {x : G | x ∈ A ∧ orderOf x = 2} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, y.property, rfl⟩, (orderOf_injective f hf y).trans hy⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      exact (orderOf_injective f hf ⟨y, hy⟩).symm.trans hx
  obtain ⟨e, he⟩ := (hdata T1).2.2.2.2.2.2.2.1
  let d : CFSG.omega₁ (G := V) (p := 2) ≃* ↥(Subgroup.zpowers u ⊔ U : Subgroup G) :=
    ((CFSG.omega₁ (G := V) (p := 2)).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hMap)
  let eA : ↥((CFSG.omega₁ (G := A) (p := 2)).map A.subtype) ≃*
      ↥(Subgroup.zpowers u ⊔ U : Subgroup G) := MulEquiv.subgroupCongr hOm
  let eV : Subgroup.zpowers u × U ≃* CFSG.omega₁ (G := V) (p := 2) :=
    (e.trans eA).trans d.symm
  refine ⟨hMap, hPre, hInv.trans (hdata T1).2.1, eV, ?_⟩
  intro a b
  have hd : (d (eV (a, b)) : G) = (e (a, b) : G) := by
    change (d (d.symm (eA (e (a, b)))) : G) = _
    rw [d.apply_symm_apply]
    rfl
  exact hd.trans (he a b)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
