module

public import CFSG.GH74.GLS.LU.Local.FiveL88a

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section L88g

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg8.L_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    ∀ g : G, g * z * g⁻¹ = u → ∀ A : Subgroup G, (A = K₁ ∨ A = K₂) →
      X5 v w₁ X₁ ≤ cjL g A → cjL g A ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  intro g hg A hA hX5
  have hc0 : (w₁ * v)⁻¹ * g ∈ centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    calc (w₁ * v)⁻¹ * g * z = (w₁ * v)⁻¹ * (g * z * g⁻¹) * g := by group
      _ = (w₁ * v)⁻¹ * u * g := by rw [hg]
      _ = (w₁ * v)⁻¹ * ((w₁ * v) * z * (w₁ * v)⁻¹) * g := by rw [c.g_z]
      _ = z * ((w₁ * v)⁻¹ * g) := by group
  have hgA : cjL g A = cjL (w₁ * v) (cjL ((w₁ * v)⁻¹ * g) A) := by
    rw [cjL_cjL, mul_inv_cancel_left]
  have hperm : (cjL ((w₁ * v)⁻¹ * g) K₁ = K₁ ∧ cjL ((w₁ * v)⁻¹ * g) K₂ = K₂) ∨
      (cjL ((w₁ * v)⁻¹ * g) K₁ = K₂ ∧ cjL ((w₁ * v)⁻¹ * g) K₂ = K₁) := c.hc.perm hc0
  have hK2 : ¬ (cjL (w₁ * v) X₁ ≤ cjL (w₁ * v) K₂) := by
    intro h
    have hX : X₁ ≤ K₂ := (cjL_le_iff _).mp h
    have h1 : X₁ ⊓ K₂ = ⊥ := c.five_inf_K2 c.b82.X₁_syl.1 c.b82.X₁_card
    have h2 : X₁ ≤ ⊥ := h1 ▸ le_inf le_rfl hX
    have hbot : X₁ = ⊥ := le_bot_iff.mp h2
    have h5 := c.b82.X₁_card
    rw [hbot, Subgroup.card_bot] at h5
    omega
  have hX5eq : X5 v w₁ X₁ = cjL (w₁ * v) X₁ := X5_eq v w₁ X₁
  have hcA : cjL ((w₁ * v)⁻¹ * g) A = K₁ ∨ cjL ((w₁ * v)⁻¹ * g) A = K₂ := by
    rcases hA with hA | hA <;> rcases hperm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [hA]
    · left; exact e1
    · right; exact e1
    · right; exact e2
    · left; exact e2
  rcases hcA with h1 | h1
  · rw [hgA, h1]
    exact c.L_P_le_N
  · exfalso
    apply hK2
    have h3 : X5 v w₁ X₁ ≤ cjL (w₁ * v) K₂ := by
      have := hX5
      rwa [hgA, h1] at this
    rwa [hX5eq] at h3

end L88g

end CFSG.GH74.GLS.LU.Local.Five
