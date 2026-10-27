module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod

import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticCommutant
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.GroupTheory.IsPerfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

theorem cl_neg_not_mem_of_sq_eq_neg {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hdim : Module.finrank (ZMod 3) V = 6)
    {T : V ≃ₗ[ZMod 3] V} (hT : ∀ v, T (T v) = -v) {J : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hJ : ⁅J, J⁆ = J) (hc : ∀ g ∈ J, g * T = T * g) : LinearEquiv.neg (ZMod 3) ∉ J := by
  let Tm : Module.End (ZMod 3) V := (T : V →ₗ[ZMod 3] V)
  have hsq : Tm ^ 2 = algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) := by
    ext v
    change (T : V →ₗ[ZMod 3] V) ((T : V →ₗ[ZMod 3] V) v) =
      (algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1)) v
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      neg_smul, one_smul]
    exact hT v
  have hJle : J ≤ operatorCentralizer Tm := by
    intro g hg x
    change g ((T : V →ₗ[ZMod 3] V) x) = (T : V →ₗ[ZMod 3] V) (g x)
    have h := congrArg (fun f : V ≃ₗ[ZMod 3] V => f x) (hc g hg)
    simpa [LinearEquiv.mul_apply] using h
  have hns : ¬ IsSquare (-1 : ZMod 3) := by decide
  haveI : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨hns⟩
  let E := extension (-1 : ZMod 3)
  letI : Module E V := actionModule Tm (-1) hsq
  haveI : CharP E 3 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 3) E) 3 (by norm_num)
  haveI : Fact (2 < 3) := ⟨by norm_num⟩
  have hfr : Module.finrank E V = 3 := by
    have h : 6 = 2 * Module.finrank E V := by
      have h' := actionModule_finrank Tm (-1) hsq
      rw [hdim] at h'
      exact h'
    omega
  let ψ : operatorCentralizer Tm ≃* (V ≃ₗ[E] V) := quadraticCentralizerEquiv Tm (-1) hsq
  let φ : J →* Eˣ :=
    (LinearEquiv.det : (V ≃ₗ[E] V) →* Eˣ).comp
      (ψ.toMonoidHom.comp (Subgroup.inclusion hJle))
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := J), _root_.commutator_def,
      Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  intro hneg
  let x : J := ⟨LinearEquiv.neg (ZMod 3), hneg⟩
  have hx1 : φ x = 1 := by
    have : x ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top x
    exact MonoidHom.mem_ker.mp this
  have hψ : ψ (Subgroup.inclusion hJle x) = LinearEquiv.smulOfUnit (-1 : Eˣ) := by
    ext v
    change (quadraticCentralizerEquiv Tm (-1) hsq (Subgroup.inclusion hJle x)) v =
      (LinearEquiv.smulOfUnit (-1 : Eˣ) : V ≃ₗ[E] V) v
    rw [quadraticCentralizerEquiv_apply]
    change (LinearEquiv.neg (ZMod 3)) v =
      (LinearEquiv.smulOfUnit (-1 : Eˣ) : V ≃ₗ[E] V) v
    simp [LinearEquiv.smulOfUnit, LinearEquiv.neg_apply]
  have hfin : (-1 : E) ^ 3 = 1 := by
    have h : LinearMap.det ((LinearEquiv.smulOfUnit (-1 : Eˣ) : V ≃ₗ[E] V) :
        V →ₗ[E] V) = 1 := by
      have h' := congrArg (fun u : Eˣ => (u : E)) hx1
      change (LinearEquiv.det (ψ (Subgroup.inclusion hJle x)) : E) = 1 at h'
      rw [LinearEquiv.coe_det, hψ] at h'
      exact h'
    have hmap : ((LinearEquiv.smulOfUnit (-1 : Eˣ) : V ≃ₗ[E] V) : V →ₗ[E] V) =
        (-1 : E) • (1 : V →ₗ[E] V) := by
      ext v
      simp [LinearEquiv.smulOfUnit, LinearMap.smul_apply]
    rw [hmap, LinearMap.det_smul, Module.End.one_eq_id, LinearMap.det_id, mul_one] at h
    rw [hfr] at h
    exact h
  have hneg1 : (-1 : E) = 1 := by
    have h3 : (-1 : E) ^ 3 = -1 := by ring
    rw [h3] at hfin
    exact hfin
  exact (CharP.neg_one_ne_one (R := E) 3) hneg1

end CFSG.OddStandard.SmallF3.Omega
