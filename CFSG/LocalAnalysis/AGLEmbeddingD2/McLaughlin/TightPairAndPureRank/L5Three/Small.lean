module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Stab
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module

@[expose] noncomputable def glStd (n : ℕ) :
    ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) ≃* GL (Fin n) (ZMod 2) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm).trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem card_linEquiv_eq {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = n) :
    Nat.card (V ≃ₗ[ZMod 2] V) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq V (Fin n → ZMod 2) (by rw [hV, Module.finrank_fin_fun])
  have h1 : Nat.card (V ≃ₗ[ZMod 2] V) = Nat.card (GL (Fin n) (ZMod 2)) :=
    Nat.card_congr (((conjGL e).trans (glStd n)).toEquiv)
  rw [h1, Matrix.card_GL_field]
  simp

theorem card_linEquiv_one {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 1) : Nat.card (V ≃ₗ[ZMod 2] V) = 1 := by
  rw [card_linEquiv_eq hV]; simp

theorem card_linEquiv_two {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 2) : Nat.card (V ≃ₗ[ZMod 2] V) = 6 := by
  rw [card_linEquiv_eq hV]; decide +kernel

theorem card_linEquiv_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 3) : Nat.card (V ≃ₗ[ZMod 2] V) = 168 := by
  rw [card_linEquiv_eq hV]; decide +kernel

theorem card_linEquiv_four {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 4) : Nat.card (V ≃ₗ[ZMod 2] V) = 20160 := by
  rw [card_linEquiv_eq hV]; decide +kernel

theorem card_linEquiv_five {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 5) : Nat.card (V ≃ₗ[ZMod 2] V) = 9999360 := by
  rw [card_linEquiv_eq hV]; decide +kernel

theorem threeBound_of_card {n N B : ℕ}
    (hN : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V], finrank (ZMod 2) V = n →
      Nat.card (V ≃ₗ[ZMod 2] V) = N)
    (hB : ∀ d, d ∣ N → ¬ 3 ∣ d → d ≤ B) : ThreeBound n B := by
  intro V _ _ _ hV Y hY
  refine hB _ ?_ hY
  rw [← hN V hV]
  exact Subgroup.card_subgroup_dvd_card Y

theorem threeBound_one : ThreeBound 1 1 :=
  threeBound_of_card (N := 1) (fun V _ _ _ h => card_linEquiv_one h)
    (fun d hd _ => Nat.le_of_dvd (by norm_num) hd)

theorem threeBound_two : ThreeBound 2 2 :=
  threeBound_of_card (N := 6) (fun V _ _ _ h => card_linEquiv_two h) (by
    intro d hd h3
    have : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp_all)

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
