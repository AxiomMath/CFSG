module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

theorem fpf_of_fpf_on_lagrangian {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (B : LinearMap.BilinForm (ZMod 2) W) (U : Submodule (ZMod 2) W)
    (hU : ∀ w : W, (∀ u ∈ U, B w u = 0) → w ∈ U)
    (f : W ≃ₗ[ZMod 2] W) (hB : ∀ x y : W, B (f x) (f y) = B x y)
    (hfU : ∀ u ∈ U, f u ∈ U) (hfix : ∀ u ∈ U, f u = u → u = 0) :
    ∀ w : W, f w = w → w = 0 := by
  intro w hw
  have horth : ∀ u ∈ U, B w u = 0 := by
    intro u hu
    let φ : U → U := fun x => ⟨f x - x, U.sub_mem (hfU x x.2) x.2⟩
    have hφinj : Function.Injective φ := by
      intro x y hxy
      have h1 : (φ x : W) = (φ y : W) := by rw [hxy]
      change f (x : W) - (x : W) = f (y : W) - (y : W) at h1
      have h2 : f ((x : W) - (y : W)) = (x : W) - (y : W) := by
        rw [map_sub]
        exact sub_eq_sub_iff_sub_eq_sub.mp h1
      have h3 : (x : W) - (y : W) = 0 := hfix _ (U.sub_mem x.2 y.2) h2
      exact Subtype.ext (sub_eq_zero.mp h3)
    have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
    obtain ⟨u₀, hu₀⟩ := hφsurj ⟨u, hu⟩
    have hval : (φ u₀ : W) = u := by rw [hu₀]
    have hzero : B w (φ u₀ : W) = 0 := by
      change B w (f (u₀ : W) - (u₀ : W)) = 0
      rw [map_sub]
      have h1 : B w (f (u₀ : W)) = B w (u₀ : W) := by
        calc B w (f (u₀ : W)) = B (f w) (f (u₀ : W)) := by rw [hw]
          _ = B w (u₀ : W) := hB w (u₀ : W)
      rw [h1, sub_self]
    rw [hval] at hzero
    exact hzero
  exact hfix w (hU w horth) hw

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
