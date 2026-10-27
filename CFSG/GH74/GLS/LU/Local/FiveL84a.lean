module

public import CFSG.GH74.GLS.LU.Local.FiveLeaves

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

structure Five84w (z t u : G) (H X₁ Y : Subgroup G) (v : G) : Prop where
  v_N : v ∈ NN z u
  v_two : IsPGroup 2 ↥(zpowers v)
  v_sq : v ^ 2 ∈ H ⊔ zpowers t
  v_z : v * z * v⁻¹ = z * u
  v_zu : v * (z * u) * v⁻¹ = z
  v_X : cjL v (XX t X₁) = Y
  v_Y : cjL v Y = XX t X₁

@[expose] def Leaf84' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∃ v : G, Five84w z t u H X₁ Y v

@[expose] def Leaf84'' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84w z t u H X₁ Y v → v ^ 2 ∈ H

theorem leaf84_of_parts (h1 : Leaf84') (h2 : Leaf84'') : Leaf84 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83
  obtain ⟨v, bw⟩ := h1 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83
  exact ⟨v, ⟨bw.v_N, bw.v_two, h2 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v bw, bw.v_z,
    bw.v_zu, bw.v_X, bw.v_Y⟩⟩

end CFSG.GH74.GLS.LU.Local.Five
