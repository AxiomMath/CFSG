module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Polynomial

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem sec12S8Mod_charTwo (x : W) : x + x = 0 := by
  have h : (2 : ZMod 2) • x = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide]
    simp
  simpa [two_smul] using h

theorem sec12S8Mod_commute_aeval (g c : Module.End (ZMod 2) W) (h : c * g = g * c)
    (p : (ZMod 2)[X]) : c * aeval g p = aeval g p * c := by
  have hc : Commute c g := h
  have hcomm : Commute c (aeval g p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add]
        exact hp.add_right hq
    | monomial n a =>
        rw [Polynomial.aeval_monomial (R := ZMod 2)]
        exact (Algebra.commute_algebraMap_right (R := ZMod 2) (A := Module.End (ZMod 2) W)
          a c).mul_right (hc.pow_right n)
  exact hcomm

theorem sec12S8Mod_conj_aeval (w : W ≃ₗ[ZMod 2] W) (G : Module.End (ZMod 2) W)
    (h : (w : Module.End (ZMod 2) W) * G * (w.symm : Module.End (ZMod 2) W) = G ^ 4)
    (q : (ZMod 2)[X]) (u : W) :
    w ((aeval G q) (w.symm u)) = aeval (G ^ 4) q u := by
  have hconjG : (w.conjAlgEquiv (ZMod 2)) G = G ^ 4 := by
    rw [LinearEquiv.conjAlgEquiv_apply]
    rw [← h]
    rfl
  have h1 := Polynomial.aeval_algHom_apply (w.conjAlgEquiv (ZMod 2)) G q
  rw [hconjG] at h1
  have h2 := congrArg (fun f : Module.End (ZMod 2) W => f u) h1
  rw [LinearEquiv.conjAlgEquiv_apply] at h2
  simpa [LinearMap.comp_apply] using h2.symm

end CFSG.OddStandard.SmallF3.Omega
