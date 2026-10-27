module

public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open QuadraticMap Module TauCeti.QuadraticMap

section Ext

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

abbrev perpOf (Q : QuadraticForm K V) (U : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) U

theorem inv_apply_apply' {M : Type*} [AddCommGroup M] [Module K M] (g : M ≃ₗ[K] M) (v : M) :
    g⁻¹ (g v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem apply_inv_apply' {M : Type*} [AddCommGroup M] [Module K M] (g : M ≃ₗ[K] M) (v : M) :
    g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

variable {Q : QuadraticForm K V} {U : Submodule K V}

theorem mem_perpOf {w : V} : w ∈ perpOf Q U ↔ ∀ u ∈ U, polar Q u w = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h u hu
    have := h u hu
    rwa [QuadraticMap.polarBilin_apply_apply] at this
  · intro h u hu
    rw [QuadraticMap.polarBilin_apply_apply]
    exact h u hu

theorem eq_of_agree (hU : IsCompl U (perpOf Q U)) {g h : V ≃ₗ[K] V}
    (h1 : ∀ u ∈ U, g u = h u) (h2 : ∀ w ∈ perpOf Q U, g w = h w) : g = h := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (by
    rw [hU.sup_eq_top]; exact Submodule.mem_top : v ∈ U ⊔ perpOf Q U)
  rw [map_add, map_add, h1 u hu, h2 w hw]

theorem map_mem_perp {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U)
    {w : V} (hw : w ∈ perpOf Q U) : g w ∈ perpOf Q U := by
  rw [mem_perpOf] at hw ⊢
  intro u hu
  have h1 := polar_apply_of_mem_orthogonalGroup hg (g⁻¹ u) w
  rw [apply_inv_apply'] at h1
  rw [h1]
  exact hw _ (hgU' u hu)

@[expose] noncomputable def resU {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q)
    (hgU : ∀ u ∈ U, g u ∈ U) (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U) :
    orthogonalGroup (Q.restrict U) :=
  ⟨g.ofSubmodules U U (by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hgU u hu
    · intro u hu
      exact ⟨g⁻¹ u, hgU' u hu, apply_inv_apply' g u⟩), by
    rw [mem_orthogonalGroup_iff]
    intro u
    change Q ((g.ofSubmodules U U _ u : U) : V) = Q (u : V)
    rw [show ((g.ofSubmodules U U _ u : U) : V) = g u from LinearEquiv.ofSubmodules_apply g _ u]
    exact map_app_of_mem_orthogonalGroup hg u⟩

theorem resU_apply {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (hgU : ∀ u ∈ U, g u ∈ U)
    (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U) (u : U) :
    ((resU hg hgU hgU').1 u : V) = g u := by
  show ((g.ofSubmodules U U _ u : U) : V) = g u
  exact LinearEquiv.ofSubmodules_apply g _ u

theorem resU_inv_apply {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (hgU : ∀ u ∈ U, g u ∈ U)
    (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U) (u : U) :
    (((resU hg hgU hgU')⁻¹.1 u : U) : V) = g⁻¹ u := by
  have h1 : (resU hg hgU hgU').1 ⟨g⁻¹ u, hgU' u u.2⟩ = u := by
    apply Subtype.ext
    rw [resU_apply, apply_inv_apply']
  have h2 : (resU hg hgU hgU')⁻¹.1 u = ⟨g⁻¹ u, hgU' u u.2⟩ := by
    have := inv_apply_apply' (resU hg hgU hgU').1 ⟨g⁻¹ u, hgU' u u.2⟩
    rw [h1] at this
    exact this
  rw [h2]

theorem fixed_map_mem {g : V ≃ₗ[K] V} (hg : ∀ u ∈ U, g u = u) {u : V} (hu : u ∈ U) :
    g u ∈ U ∧ g⁻¹ u ∈ U := by
  refine ⟨by rw [hg u hu]; exact hu, ?_⟩
  have h : g⁻¹ u = u := by
    conv_lhs => rw [← hg u hu]
    exact inv_apply_apply' g u
  rw [h]
  exact hu

section ExtMap

variable (hU : IsCompl U (perpOf Q U))
include hU

@[expose] noncomputable def extU :
    orthogonalGroup (Q.restrict U) →* orthogonalGroup Q :=
  ((orthogonalGroupCongr (IsometryEquiv.prodRestrictOrthogonal Q U hU)).toMonoidHom.comp
    (orthogonalGroupProd (Q.restrict U) (Q.restrict (perpOf Q U)))).comp (MonoidHom.inl _ _)

theorem extU_apply (φ : orthogonalGroup (Q.restrict U)) (v : V) :
    ((extU hU φ).1 : V ≃ₗ[K] V) v =
      ((φ.1 (U.projectionOnto _ hU v) : U) : V) +
        (((perpOf Q U).projectionOnto U hU.symm v : perpOf Q U) : V) := by
  simp [extU]

theorem extU_apply_of_mem_U (φ : orthogonalGroup (Q.restrict U)) {u : V} (hu : u ∈ U) :
    ((extU hU φ).1 : V ≃ₗ[K] V) u = ((φ.1 ⟨u, hu⟩ : U) : V) := by
  rw [extU_apply hU, Submodule.projectionOnto_apply_of_mem_left hU hu,
    Submodule.projectionOnto_apply_of_mem_right hU.symm hu]
  simp

theorem extU_apply_of_mem_perp (φ : orthogonalGroup (Q.restrict U)) {w : V}
    (hw : w ∈ perpOf Q U) : ((extU hU φ).1 : V ≃ₗ[K] V) w = w := by
  rw [extU_apply hU, Submodule.projectionOnto_apply_of_mem_right hU hw,
    Submodule.projectionOnto_apply_of_mem_left hU.symm hw]
  simp

theorem extU_injective : Function.Injective (extU hU) := by
  intro φ ψ h
  have key : ∀ u : U, φ.1 u = ψ.1 u := by
    intro u
    have := congrArg (fun g : orthogonalGroup Q => (g.1 : V ≃ₗ[K] V) (u : V)) h
    rw [extU_apply_of_mem_U hU φ u.2, extU_apply_of_mem_U hU ψ u.2] at this
    exact Subtype.ext this
  exact Subtype.ext (LinearEquiv.ext key)

theorem conj_extU {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (hgU : ∀ u ∈ U, g u ∈ U)
    (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U) (φ : orthogonalGroup (Q.restrict U)) :
    g * (extU hU φ).1 * g⁻¹ =
      (extU hU (resU hg hgU hgU' * φ * (resU hg hgU hgU')⁻¹)).1 := by
  apply eq_of_agree hU
  · intro u hu
    have hgi : g⁻¹ u ∈ U := hgU' u hu
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, extU_apply_of_mem_U hU φ hgi,
      extU_apply_of_mem_U hU _ hu]
    have e1 := resU_inv_apply hg hgU hgU' ⟨u, hu⟩
    have e2 : (((resU hg hgU hgU' * φ * (resU hg hgU hgU')⁻¹).1 ⟨u, hu⟩ : U) : V) =
        g ((φ.1 ⟨g⁻¹ u, hgi⟩ : U) : V) := by
      show (((resU hg hgU hgU').1 (φ.1 ((resU hg hgU hgU')⁻¹.1 ⟨u, hu⟩)) : U) : V) = _
      rw [resU_apply]
      congr 2
    rw [e2]
  · intro w hw
    have hgi : g⁻¹ w ∈ perpOf Q U := by
      have := map_mem_perp (g := g⁻¹) (inv_mem hg) (by simpa using hgU) hw
      exact this
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, extU_apply_of_mem_perp hU φ hgi,
      extU_apply_of_mem_perp hU _ hw, apply_inv_apply']

theorem extU_commute {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (hgfix : ∀ u ∈ U, g u = u)
    (φ : orthogonalGroup (Q.restrict U)) : (extU hU φ).1 * g = g * (extU hU φ).1 := by
  have hgU' : ∀ u ∈ U, g⁻¹ u ∈ U := fun u hu => (fixed_map_mem hgfix hu).2
  apply eq_of_agree hU
  · intro u hu
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgfix u hu,
      extU_apply_of_mem_U hU φ hu, hgfix _ (φ.1 ⟨u, hu⟩).2]
  · intro w hw
    have hgw : g w ∈ perpOf Q U := map_mem_perp hg hgU' hw
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, extU_apply_of_mem_perp hU φ hw,
      extU_apply_of_mem_perp hU φ hgw]

end ExtMap

end Ext

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
