module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockMap_mul {σ τ : Perm (ι × Bool)} (hσ : σ ∈ blockStab ι) (hτ : τ ∈ blockStab ι) :
    blockMap (σ * τ) ((blockStab ι).mul_mem hσ hτ) = blockMap σ hσ * blockMap τ hτ := by
  ext a
  show blockMap (σ * τ) _ a = blockMap σ hσ (blockMap τ hτ a)
  have h1 : blockMap (σ * τ) ((blockStab ι).mul_mem hσ hτ) a = (σ (τ (a, false))).1 :=
    blockMap_apply _ (a, false)
  have h2 : blockMap τ hτ a = (τ (a, false)).1 := blockMap_apply hτ (a, false)
  have h3 : blockMap σ hσ (τ (a, false)).1 = (σ (τ (a, false))).1 := blockMap_apply hσ (τ (a, false))
  rw [h1, h2, h3]

theorem mem_blockFix_of_blockMap_eq_one {σ : Perm (ι × Bool)} (hσ : σ ∈ blockStab ι)
    (h : blockMap σ hσ = 1) : σ ∈ blockFix ι := by
  intro x
  have := blockMap_apply hσ x
  rw [h] at this
  exact this.symm

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
