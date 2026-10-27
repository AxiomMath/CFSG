module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll centralizerPerfectCore_eq_map_of_le)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective
  planeTorusParam range_planeEnum range_sumMap_eq_planeCoords)

section Glue

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d} (h : IsHypFrame Q a b)
  (e : L ≃* matrixProjectiveDerived Q) {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type}
  [Field F]

include h in
theorem exists_param_of_mem_modelToG_frameTorusOf {P : Subgroup (Fin m → Kˣ)} {x : G}
    (hx : x ∈ modelToG e (frameTorusOf Q a b P)) :
    ∃ t ∈ P, ((e.symm (h.frameHom t) : L) : G) = x := by
  rw [h.frameTorusOf_eq_map] at hx
  obtain ⟨y, ⟨t, ht, rfl⟩, rfl⟩ := (mem_modelToG e).1 hx
  exact ⟨t, ht, rfl⟩

omit [Finite K] [CharP K 2] in
theorem map_fixAll_normalizerMonoidHom_eq_frame [Finite K] [CharP K 2]
    {H : Subgroup (GL ι F)} (δ : (Fin m → Kˣ) →* GL ι F)
    (hδ : ∀ t, δ t ∈ normalizer (H : Set (GL ι F))) {P : Subgroup (Fin m → Kˣ)}
    (τ : modelToG e (frameTorusOf Q a b P) → Fin m → Kˣ)
    (hτ : ∀ x, τ x ∈ P ∧ ((e.symm (h.frameHom (τ x)) : L) : G) = x) :
    (fixAll fun x => H.normalizerMonoidHom ⟨δ (τ x), hδ (τ x)⟩).map H.subtype =
      H ⊓ centralizer (δ '' (P : Set (Fin m → Kˣ))) := by
  have hsurj : ∀ t ∈ P, ∃ x, τ x = t := by
    intro t ht
    let x : modelToG e (frameTorusOf Q a b P) :=
      ⟨((e.symm (h.frameHom t) : L) : G),
        symm_mem_modelToG e (h.frameHom_mem_frameTorusOf ht)⟩
    refine ⟨x, ?_⟩
    have h' : e.symm (h.frameHom (τ x)) = e.symm (h.frameHom t) := Subtype.ext (hτ x).2
    exact h.frameHom_injective (e.symm.injective h')
  ext y
  simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj t ht
    have hc : δ (τ x) * (z : GL ι F) * (δ (τ x))⁻¹ = z :=
      congrArg Subtype.val (mem_fixAll.1 hz x)
    calc δ (τ x) * (z : GL ι F) = δ (τ x) * (z : GL ι F) * (δ (τ x))⁻¹ * δ (τ x) := by group
      _ = (z : GL ι F) * δ (τ x) := by rw [hc]
  · rintro ⟨hyH, hy⟩
    refine ⟨⟨y, hyH⟩, mem_fixAll.2 fun x => Subtype.ext ?_, rfl⟩
    change δ (τ x) * y * (δ (τ x))⁻¹ = y
    rw [hy _ ⟨τ x, (hτ x).1, rfl⟩, mul_inv_cancel_right]

variable [Finite G] [Finite F]

end Glue

end CFSG.SeitzReduction.OmegaPilot
