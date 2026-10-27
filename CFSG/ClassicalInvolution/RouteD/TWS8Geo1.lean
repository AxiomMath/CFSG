module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Gen
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small (stabSub)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Plane

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def wPlane (fr : OFrame Q) : Submodule F V := LinearMap.range fr.incl

theorem mem_wPlane {fr : OFrame Q} {x : V} : x ∈ wPlane fr ↔ x = fr.incl (fr.coords x) := by
  constructor
  · rintro ⟨X, rfl⟩
    rw [Frame.coords_incl]
  · intro h
    exact ⟨_, h.symm⟩

theorem incl_mem_wPlane (fr : OFrame Q) (X : Matrix (Fin 2) (Fin 2) F) :
    fr.incl X ∈ wPlane fr := ⟨X, rfl⟩

theorem sub_incl_mem_perp (fr : OFrame Q) (x : V) : x - fr.incl (fr.coords x) ∈ fr.perp := by
  rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]

theorem polar_perp_wPlane {fr : OFrame Q} {a w : V} (ha : a ∈ fr.perp) (hw : w ∈ wPlane fr) :
    polar Q a w = 0 := by
  obtain ⟨Y, rfl⟩ := hw
  rw [Frame.polar_incl_right, (Frame.mem_perp_iff fr).mp ha]
  simp

theorem polar_wPlane_perp {fr : OFrame Q} {a w : V} (ha : a ∈ fr.perp) (hw : w ∈ wPlane fr) :
    polar Q w a = 0 := by
  rw [polar_comm]
  exact polar_perp_wPlane ha hw

theorem e₁_mem_wPlane (fr : OFrame Q) : fr.e₁ ∈ wPlane fr :=
  ⟨!![1, 0; 0, 0], by simp [Frame.incl_apply]⟩

theorem f₁_mem_wPlane (fr : OFrame Q) : fr.f₁ ∈ wPlane fr :=
  ⟨!![0, 0; 0, 1], by simp [Frame.incl_apply]⟩

@[expose] def stabE (fr : OFrame Q) : Subgroup (V ≃ₗ[F] V) :=
  elementaryGroup Q ⊓ stabSub (wPlane fr)

theorem mem_stabE {fr : OFrame Q} {g : V ≃ₗ[F] V} :
    g ∈ stabE fr ↔ g ∈ elementaryGroup Q ∧ ∀ x, x ∈ wPlane fr ↔ g x ∈ wPlane fr :=
  Iff.rfl

theorem eichler_mem_stabE (fr : OFrame Q) {u w : V} (hu : u ∈ wPlane fr) (hw : w ∈ wPlane fr) :
    eichler Q u w ∈ stabE fr := by
  refine ⟨eichler_mem_elementaryGroup Q u w, fun x => ?_⟩
  obtain ⟨a, b, hab⟩ := eichler_apply_eq_add (Q := Q) u w x
  rw [hab, add_assoc]
  have h1 : a • w + b • u ∈ wPlane fr :=
    (wPlane fr).add_mem ((wPlane fr).smul_mem a hw) ((wPlane fr).smul_mem b hu)
  constructor
  · intro hx
    exact (wPlane fr).add_mem hx h1
  · intro hx
    have h2 := (wPlane fr).sub_mem hx h1
    simpa using h2

theorem mem_stabSub_of_mapsTo [FiniteDimensional F V] {W : Submodule F V} {g : V ≃ₗ[F] V}
    (h : ∀ x ∈ W, g x ∈ W) : ∀ x, x ∈ W ↔ g x ∈ W := by
  have hle : W.map (g : V →ₗ[F] V) ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hrank : Module.finrank F (W.map (g : V →ₗ[F] V)) = Module.finrank F W :=
    LinearEquiv.finrank_map_eq g W
  have heq : W.map (g : V →ₗ[F] V) = W := Submodule.eq_of_le_of_finrank_eq hle hrank
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := g.injective hyx
  rw [← this]
  exact hy

theorem decomp_wPlane (fr : OFrame Q) {y : V} (hy : y ∈ wPlane fr) :
    ∃ y₂ ∈ wPlane fr, polar Q y₂ fr.e₁ = 0 ∧
      y = polar Q y fr.f₁ • fr.e₁ + polar Q y fr.e₁ • fr.f₁ + y₂ := by
  refine ⟨y - polar Q y fr.f₁ • fr.e₁ - polar Q y fr.e₁ • fr.f₁,
    (wPlane fr).sub_mem ((wPlane fr).sub_mem hy ((wPlane fr).smul_mem _ (e₁_mem_wPlane fr)))
      ((wPlane fr).smul_mem _ (f₁_mem_wPlane fr)), ?_, by abel⟩
  have hee : polar Q fr.e₁ fr.e₁ = 0 := polar_self_eq_zero fr.Q_e₁
  rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hee,
    fr.polar_f₁_e₁]
  ring

end Plane

section Fix

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V]

theorem exists_mixed_of_fix (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    {k : V ≃ₗ[F] V} (hk : k ∈ H) (hkE : k ∈ elementaryGroup Q) (hke : k fr.e₁ = fr.e₁)
    (hkW : ¬ ∀ x ∈ wPlane fr, k x ∈ wPlane fr) :
    ∃ a ∈ fr.perp, a ≠ 0 ∧ eichler Q fr.e₁ a ∈ H := by
  classical
  have hkO : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hkE
  have hQe : Q fr.e₁ = 0 := fr.Q_e₁
  have hee : polar Q fr.e₁ fr.e₁ = 0 := polar_self_eq_zero hQe
  have heW := e₁_mem_wPlane fr
  have hfW := f₁_mem_wPlane fr
  have hEu : ∀ u ∈ wPlane fr, eichler Q fr.e₁ u ∈ H := fun u hu =>
    hH (eichler_mem_stabE fr heW hu)
  have hconj : ∀ w, k * eichler Q fr.e₁ w * k⁻¹ = eichler Q fr.e₁ (k w) := fun w => by
    rw [eichler_conj hkO, hke]
  have hpol : ∀ y, polar Q (k y) fr.e₁ = polar Q y fr.e₁ := fun y => by
    have := polar_map_of_mem hkO y fr.e₁
    rwa [hke] at this
  by_cases hφ : ∀ w ∈ wPlane fr, polar Q w fr.e₁ = 0 → k w ∈ wPlane fr
  ·
    set η : V := k fr.f₁ - fr.f₁ with hη
    have hηe : polar Q fr.e₁ η = 0 := by
      rw [polar_comm, hη, polar_sub_left, hpol, fr.polar_f₁_e₁, sub_self]
    set ηW : V := fr.incl (fr.coords η) with hηW
    set a₁ : V := η - ηW with ha₁
    have ha₁perp : a₁ ∈ fr.perp := sub_incl_mem_perp fr η
    have hηWe : polar Q fr.e₁ ηW = 0 := by
      have h1 : polar Q fr.e₁ a₁ = 0 := by
        rw [polar_comm]
        exact polar_perp_wPlane ha₁perp heW
      have h2 : polar Q fr.e₁ η = polar Q fr.e₁ ηW + polar Q fr.e₁ a₁ := by
        rw [ha₁, ← polar_add_right]
        congr 1
        abel
      rw [h2, h1, add_zero] at hηe
      exact hηe
    have hηsplit : η = ηW + a₁ := by rw [ha₁]; abel
    set k₁ : V ≃ₗ[F] V := eichler Q fr.e₁ (-η) * k with hk₁
    have hηe' : polar Q fr.e₁ (-η) = 0 := by rw [polar_neg_right, hηe, neg_zero]
    have hk₁e : k₁ fr.e₁ = fr.e₁ := by
      rw [hk₁, LinearEquiv.mul_apply, hke]
      exact eichler_apply_self fr.e₁ (-η)
    have hk₁f : k₁ fr.f₁ ∈ wPlane fr := by
      rw [hk₁, LinearEquiv.mul_apply, eichler_apply hQe hηe']
      have h3 : polar Q (k fr.f₁) fr.e₁ = 1 := by rw [hpol, fr.polar_f₁_e₁]
      rw [h3]
      have h4 : k fr.f₁ + (1 : F) • (-η) = fr.f₁ := by
        rw [hη]
        simp
      rw [one_smul] at *
      have h5 : k fr.f₁ + -η - (polar Q (k fr.f₁) (-η) + Q (-η) * 1) • fr.e₁ =
          fr.f₁ - (polar Q (k fr.f₁) (-η) + Q (-η) * 1) • fr.e₁ := by
        rw [← sub_eq_add_neg] at *
        rw [hη]
        abel
      rw [h5]
      exact (wPlane fr).sub_mem hfW ((wPlane fr).smul_mem _ heW)
    have hk₁y : ∀ y ∈ wPlane fr, polar Q y fr.e₁ = 0 → k₁ y ∈ wPlane fr := by
      intro y hy hye
      have hky : k y ∈ wPlane fr := hφ y hy hye
      rw [hk₁, LinearEquiv.mul_apply, eichler_apply hQe hηe', hpol, hye, zero_smul, add_zero]
      exact (wPlane fr).sub_mem hky ((wPlane fr).smul_mem _ heW)
    have hk₁W : ∀ y ∈ wPlane fr, k₁ y ∈ wPlane fr := by
      intro y hy
      obtain ⟨y₂, hy₂, hy₂e, hysplit⟩ := decomp_wPlane fr hy
      rw [hysplit, map_add, map_add, map_smul, map_smul, hk₁e]
      refine (wPlane fr).add_mem ((wPlane fr).add_mem ((wPlane fr).smul_mem _ heW)
        ((wPlane fr).smul_mem _ hk₁f)) (hk₁y y₂ hy₂ hy₂e)
    have hk₁mem : k₁ ∈ stabE fr := by
      refine ⟨(elementaryGroup Q).mul_mem ?_ hkE, mem_stabSub_of_mapsTo hk₁W⟩
      exact eichler_mem_elementaryGroup Q _ _
    have hk₁H : k₁ ∈ H := hH hk₁mem
    have hxH : eichler Q fr.e₁ (-η) ∈ H := by
      have : eichler Q fr.e₁ (-η) = k₁ * k⁻¹ := by rw [hk₁]; group
      rw [this]
      exact H.mul_mem hk₁H (H.inv_mem hk)
    have hEη : eichler Q fr.e₁ η ∈ H := by
      have := H.inv_mem hxH
      rwa [eichler_inv hηe', neg_neg] at this
    have hEa₁ : eichler Q fr.e₁ a₁ ∈ H := by
      have hηWmem : ηW ∈ wPlane fr := incl_mem_wPlane fr _
      have h6 : eichler Q fr.e₁ ηW * eichler Q fr.e₁ a₁ = eichler Q fr.e₁ η := by
        have h7 : polar Q fr.e₁ a₁ = 0 := by
          rw [polar_comm]
          exact polar_perp_wPlane ha₁perp heW
        rw [eichler_mul hηWe h7, ← hηsplit]
      have h8 : eichler Q fr.e₁ a₁ = (eichler Q fr.e₁ ηW)⁻¹ * eichler Q fr.e₁ η := by
        rw [← h6]; group
      rw [h8]
      exact H.mul_mem (H.inv_mem (hEu ηW hηWmem)) hEη
    refine ⟨a₁, ha₁perp, fun ha0 => hkW ?_, hEa₁⟩
    have hηWeq : η = ηW := by rw [hηsplit, ha0, add_zero]
    have hηmem : η ∈ wPlane fr := by rw [hηWeq]; exact incl_mem_wPlane fr _
    have hkf : k fr.f₁ ∈ wPlane fr := by
      have : k fr.f₁ = fr.f₁ + η := by rw [hη]; abel
      rw [this]
      exact (wPlane fr).add_mem hfW hηmem
    intro y hy
    obtain ⟨y₂, hy₂, hy₂e, hysplit⟩ := decomp_wPlane fr hy
    rw [hysplit, map_add, map_add, map_smul, map_smul, hke]
    exact (wPlane fr).add_mem ((wPlane fr).add_mem ((wPlane fr).smul_mem _ heW)
      ((wPlane fr).smul_mem _ hkf)) (hφ y₂ hy₂ hy₂e)
  ·
    push Not at hφ
    obtain ⟨w, hwW, hwe, hkw⟩ := hφ
    set u : V := fr.incl (fr.coords (k w)) with hu
    set a : V := k w - u with ha
    have haperp : a ∈ fr.perp := sub_incl_mem_perp fr (k w)
    have hsplit : k w = u + a := by rw [ha]; abel
    have hae : polar Q fr.e₁ a = 0 := by
      rw [polar_comm]
      exact polar_perp_wPlane haperp heW
    have hkwe : polar Q fr.e₁ (k w) = 0 := by rw [polar_comm, hpol, hwe]
    have hue : polar Q fr.e₁ u = 0 := by
      have h2 : polar Q fr.e₁ (k w) = polar Q fr.e₁ u + polar Q fr.e₁ a := by
        rw [← polar_add_right, ← hsplit]
      rw [h2, hae, add_zero] at hkwe
      exact hkwe
    have humem : u ∈ wPlane fr := incl_mem_wPlane fr _
    have hEw : eichler Q fr.e₁ (k w) ∈ H := by
      rw [← hconj]
      exact H.mul_mem (H.mul_mem hk (hEu w hwW)) (H.inv_mem hk)
    have h6 : eichler Q fr.e₁ u * eichler Q fr.e₁ a = eichler Q fr.e₁ (k w) := by
      rw [eichler_mul hue hae, ← hsplit]
    have h8 : eichler Q fr.e₁ a = (eichler Q fr.e₁ u)⁻¹ * eichler Q fr.e₁ (k w) := by
      rw [← h6]; group
    refine ⟨a, haperp, fun ha0 => hkw ?_, ?_⟩
    · rw [hsplit, ha0, add_zero]
      exact incl_mem_wPlane fr _
    · rw [h8]
      exact H.mul_mem (H.inv_mem (hEu u humem)) hEw

end Fix

end CFSG.ClassicalInvolution.RouteD.TWS8
