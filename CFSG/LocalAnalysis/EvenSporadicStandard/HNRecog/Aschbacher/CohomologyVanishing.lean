module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Rigidity
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Cocycle

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.crossedHomVanishing_commutator [Finite C] (hC : AschbacherHyp C Q) :
    letI := hC.plus.finite
    CrossedHomVanishing hC.plus.isExtraspecialPGroup (commutator C) := by
  classical
  letI := hC.plus.finite
  show CrossedHomVanishing hC.plus.isExtraspecialPGroup (commutator C)
  unfold CrossedHomVanishing
  intro d hd hd0
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  obtain ⟨θ, σ, hθsurj, hθker, hσθ, hσinj, hσirr⟩ := hC.exists_hom
  have hcoe : ∀ g : C,
      ((extraspecialConjOrth hC.plus.isExtraspecialPGroup hQn g :
        TauCeti.QuadraticMap.orthogonalGroup
          (extraspecialQuadForm hC.plus.isExtraspecialPGroup)) :
        Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) =
      conjLinEquiv hQn g := fun g => rfl
  have hd' : ∀ l l' : ↥(commutator C),
      d (l * l') = d l + conjLinEquiv hQn (l : C) (d l') := fun l l' => by
    simpa only [hcoe l] using hd l l'
  let dbar : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →
      Additive (Abelianization Q) := fun g => d (Function.surjInv hθsurj g)
  have hdbar_theta : ∀ l : ↥(commutator C), dbar (θ l) = d l := by
    intro l
    let l' : ↥(commutator C) := Function.surjInv hθsurj (θ l)
    have hθl' : θ l' = θ l := Function.surjInv_eq hθsurj (θ l)
    let c : ↥(commutator C) := l⁻¹ * l'
    have hlc : l * c = l' := by
      show l * (l⁻¹ * l') = l'
      group
    have hθc : θ c = 1 := by
      show θ (l⁻¹ * l') = 1
      rw [map_mul, map_inv, hθl', inv_mul_cancel]
    have hcQ : (c : C) ∈ Q := (hθker c).1 hθc
    have hdc : d c = 0 := hd0 c hcQ
    calc dbar (θ l) = d l' := rfl
      _ = d (l * c) := by rw [hlc]
      _ = d l + conjLinEquiv hQn (l : C) (d c) := hd' l c
      _ = d l := by rw [hdc, map_zero, add_zero]
  have hdbar_mul : ∀ g h : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      dbar (g * h) = dbar g + σ g (dbar h) := by
    intro g h
    let lg : ↥(commutator C) := Function.surjInv hθsurj g
    let lh : ↥(commutator C) := Function.surjInv hθsurj h
    have hθlg : θ lg = g := Function.surjInv_eq hθsurj g
    have hθlh : θ lh = h := Function.surjInv_eq hθsurj h
    have hθlgh : θ (lg * lh) = g * h := by rw [map_mul, hθlg, hθlh]
    calc dbar (g * h) = dbar (θ (lg * lh)) := by rw [hθlgh]
      _ = d (lg * lh) := hdbar_theta (lg * lh)
      _ = d lg + conjLinEquiv hQn (lg : C) (d lh) := hd' lg lh
      _ = dbar g + σ g (dbar h) := by
            rw [← hdbar_theta lg, ← hdbar_theta lh, ← hσθ lg, hθlg, hθlh]
  have h8 : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hC.plus.finrank_quotient]
  obtain ⟨hα, hβ⟩ := Fpf.fixedFree_of_irreducible σ hσinj h8 hσirr
  obtain ⟨v, hv⟩ := Fpf.exists_coboundary_of_fixedFree σ hα hβ dbar hdbar_mul
  refine ⟨v, fun l => ?_⟩
  have h1 : d l = conjLinEquiv hQn (l : C) v + v := by
    rw [← hdbar_theta l, ← hσθ l]
    exact hv (θ l)
  simpa only [hcoe l] using h1

end CFSG.EvenSporadicStandard.HNRecog
