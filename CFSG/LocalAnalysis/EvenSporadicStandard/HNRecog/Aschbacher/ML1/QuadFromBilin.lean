module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']

theorem quad_isometry_of_bilin (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')) (q : QuadraticForm (ZMod 2) V) (q' : QuadraticForm (ZMod 2) V')
    (hS : Swap.StdHyp σ) (hq : ∀ g u, q (σ g u) = q u) (hq' : ∀ g u, q' (σ' g u) = q' u)
    (a : V ≃ₗ[ZMod 2] V') (hB : ∀ x y, q'.polarBilin (a x) (a y) = q.polarBilin x y)
    (hint : ∀ g u, a (σ g u) = σ' g (a u)) : ∀ u, q' (a u) = q u := by
  have hpp : ∀ p : ZMod 2, p + p = 0 := by decide
  have hcc : ∀ c : ZMod 2, c * c = c := by decide
  let δ : V →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => q' (a u) + q u
      map_add' := by
        intro x y
        have hp : QuadraticMap.polar q' (a x) (a y) = QuadraticMap.polar q x y := by
          have h := hB x y
          rwa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
        rw [LinearEquiv.map_add a x y,
          QuadraticMap.map_add q' (a x) (a y), QuadraticMap.map_add q x y, hp]
        have hcancel : (q' (a x) + q' (a y) + QuadraticMap.polar q x y)
            + (q x + q y + QuadraticMap.polar q x y)
            = (q' (a x) + q' (a y)) + (q x + q y) + (QuadraticMap.polar q x y + QuadraticMap.polar q x y) := by
          abel
        rw [hcancel, hpp (QuadraticMap.polar q x y), add_zero]
        abel
      map_smul' := by
        intro c x
        rw [LinearEquiv.map_smul a c x,
          QuadraticMap.map_smul q' c (a x), QuadraticMap.map_smul q c x, hcc c]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
  have hInv : ∀ g : A5 × A5, ∀ u ∈ LinearMap.ker δ, σ g u ∈ LinearMap.ker δ := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    change q' (a (σ g u)) + q (σ g u) = 0
    rw [hint g u, hq' g (a u), hq g u]
    exact hu
  rcases hS.irr (LinearMap.ker δ) hInv with hbot | htop
  · have hinj : Function.Injective δ := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hS.finrank_eq, Module.finrank_self] at hle
    omega
  · intro u
    have hu : u ∈ LinearMap.ker δ := by rw [htop]; trivial
    rw [LinearMap.mem_ker] at hu
    exact CharTwo.add_eq_zero.mp hu

end CFSG.EvenSporadicStandard.HNRecog.ML1
