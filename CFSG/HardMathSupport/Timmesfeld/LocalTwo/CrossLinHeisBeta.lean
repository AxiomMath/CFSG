module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisAlg

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

@[expose] def betaOp (p : ℕ) (t ti : Module.End K V) (y : V) (ξ : Module.Dual K V) :
    Module.End K V :=
  ∑ k ∈ Finset.range p, (ξ.comp (ti ^ k)).smulRight ((t ^ k) y)

theorem betaOp_apply (y : V) (ξ : Module.Dual K V) (v : V) :
    betaOp p t ti y ξ v = ∑ k ∈ Finset.range p, ξ ((ti ^ k) v) • (t ^ k) y := by
  simp [betaOp, LinearMap.sum_apply]

theorem sum_range_shift {p : ℕ} (g : ℕ → Module.End K V) (hg : g p = g 0) :
    ∑ k ∈ Finset.range p, g (k + 1) = ∑ k ∈ Finset.range p, g k := by
  have h1 := Finset.sum_range_succ g p
  have h2 := Finset.sum_range_succ' g p
  rw [hg] at h1
  have : ∑ k ∈ Finset.range p, g (k + 1) + g 0 = ∑ k ∈ Finset.range p, g k + g 0 := by
    rw [← h2, h1]
  exact add_right_cancel this

namespace HeisData

variable (H : HeisData p f t ti c₀)

include H

theorem betaOp_comm [Nontrivial V] (y : V) (ξ : Module.Dual K V) :
    betaOp p t ti y ξ * t = t * betaOp p t ti y ξ := by
  set N : Module.End K V := ξ.smulRight y with hN
  have hterm : ∀ k : ℕ, (ξ.comp (ti ^ k)).smulRight ((t ^ k) y) = t ^ k * N * ti ^ k := by
    intro k
    refine LinearMap.ext fun v => ?_
    simp [hN, Module.End.mul_apply]
  have hβ : betaOp p t ti y ξ = ∑ k ∈ Finset.range p, t ^ k * N * ti ^ k := by
    simp only [betaOp, hterm]
  have hconj : t * betaOp p t ti y ξ * ti = betaOp p t ti y ξ := by
    rw [hβ, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k : ℕ, t * (t ^ k * N * ti ^ k) * ti = t ^ (k + 1) * N * ti ^ (k + 1) := by
      intro k
      rw [pow_succ', pow_succ]
      simp only [mul_assoc]
    simp only [this]
    refine sum_range_shift (fun k => t ^ k * N * ti ^ k) ?_
    simp only [pow_zero, one_mul, mul_one]
    rw [H.tp, H.ti_pow_p, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul,
      inv_mul_cancel₀ H.c₀_ne_zero, one_smul]
  calc betaOp p t ti y ξ * t = t * betaOp p t ti y ξ * ti * t := by rw [hconj]
    _ = t * betaOp p t ti y ξ := by rw [mul_assoc, H.ti_t, mul_one]

end HeisData

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
