module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM19
public import CFSG.ClassicalInvolution.Asc77.AscC5OM18

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem exc_conj [Finite F] (h2 : (2 : F) ≠ 0) (β₁ β₂ : Y ≃* Y) (M₁ M₂ : gsp 2 F)
    (hβ₁ : ∀ x, β₁ (fr.ψ x) = fr.ψ (conjSp 2 F M₁ x))
    (hβ₂ : ∀ x, β₂ (fr.ψ x) = fr.ψ (conjSp 2 F M₂ x)) (hns₁ : ¬ IsSquare (mu M₁))
    (hns₂ : ¬ IsSquare (mu M₂)) (hN₁ : gm M₁ * gm M₁ = (-mu M₁) • 1)
    (hN₂ : gm M₂ * gm M₂ = (-mu M₂) • 1) :
    ∃ g : Y, ∀ x : Y, β₂ x = g * β₁ (g⁻¹ * x * g) * g⁻¹ := by
  obtain ⟨c, hc⟩ := exists_unit_mul_self_mul h2 (Units.ne_zero (multiplier 2 F M₁))
    (Units.ne_zero (multiplier 2 F M₂)) hns₁ hns₂
  set M₃ := smulGsp c M₂ with hM₃
  have hmu₃ : mu M₃ = mu M₁ := by rw [hM₃, mu_smulGsp, hc]
  have hN₃ : gm M₃ * gm M₃ = (-mu M₃) • 1 := by
    rw [hM₃, gm_smulGsp, Matrix.smul_mul, Matrix.mul_smul, hN₂, smul_smul, mu_smulGsp,
      smul_smul]
    congr 1
    ring
  obtain ⟨g₁, hg₁⟩ := exists_conj_nMinus h2 hN₁
  obtain ⟨g₂, hg₂⟩ := exists_conj_nMinus h2 hN₃
  rw [hmu₃] at hg₂
  obtain ⟨h, hh⟩ : ∃ h : StatedSp 2 F, h = g₂ * g₁⁻¹ := ⟨_, rfl⟩
  have hinv : ∀ g : StatedSp 2 F, mat 2 F g * mat 2 F g⁻¹ = 1 := fun g => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ g : StatedSp 2 F, mat 2 F g⁻¹ * mat 2 F g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hint : gm M₃ * mat 2 F h = mat 2 F h * gm M₁ := by
    have e₁ : gm M₁ = mat 2 F g₁ * nMinus (mu M₁) * mat 2 F g₁⁻¹ := by
      rw [hg₁, Matrix.mul_assoc, hinv, Matrix.mul_one]
    have e₂ : gm M₃ = mat 2 F g₂ * nMinus (mu M₁) * mat 2 F g₂⁻¹ := by
      rw [hg₂, Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [hh, map_mul, e₁, e₂]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (mat 2 F g₂⁻¹) (mat 2 F g₂), hinv', Matrix.one_mul,
      ← Matrix.mul_assoc (mat 2 F g₁⁻¹) (mat 2 F g₁), hinv', Matrix.one_mul]
  refine ⟨fr.ψ h, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := fr.surj y
  have e : fr.ψ (h⁻¹ * x * h) = (fr.ψ h)⁻¹ * fr.ψ x * fr.ψ h := by
    rw [map_mul, map_mul, map_inv]
  rw [hβ₂, ← conjSp_smulGsp c, ← hM₃, conjSp_eq_of_intertwine M₁ M₃ h hint, map_mul, map_mul,
    map_inv, ← hβ₁, e]

theorem excClass [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hodd : Odd (Nat.card F)) (β₁ β₂ : Y ≃* Y)
    (hβ₁2 : ∀ x, β₁ (β₁ x) = x) (hβ₂2 : ∀ x, β₂ (β₂ x) = x)
    (hfix₁ : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₁ x ≠ x)
    (hfix₂ : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₂ x ≠ x)
    (hbig₁ : ¬ ∃ L : Subgroup Y, (∀ x ∈ L, β₁ x = x) ∧ IsSimpleGroup L ∧
      (∃ x y : L, x * y ≠ y * x) ∧ Nat.card SL(2, F) ^ 2 < 4 * Nat.card L)
    (hbig₂ : ¬ ∃ L : Subgroup Y, (∀ x ∈ L, β₂ x = x) ∧ IsSimpleGroup L ∧
      (∃ x y : L, x * y ≠ y * x) ∧ Nat.card SL(2, F) ^ 2 < 4 * Nat.card L) :
    ∃ g : Y, ∀ x : Y, β₂ x = g * β₁ (g⁻¹ * x * g) * g⁻¹ := by
  obtain ⟨M₁, hM₁, hns₁, h₁⟩ := fr.exc_shape hp h2 h4 β₁ hβ₁2 hfix₁
  obtain ⟨M₂, hM₂, hns₂, h₂⟩ := fr.exc_shape hp h2 h4 β₂ hβ₂2 hfix₂
  rcases h₁ with h₁ | h₁
  · exact absurd (fr.hasBigFix_of_plus h2 h4 hodd β₁ M₁ hM₁ hns₁ h₁) hbig₁
  rcases h₂ with h₂ | h₂
  · exact absurd (fr.hasBigFix_of_plus h2 h4 hodd β₂ M₂ hM₂ hns₂ h₂) hbig₂
  exact fr.exc_conj h2 β₁ β₂ M₁ M₂ hM₁ hM₂ hns₁ hns₂ h₁ h₂

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
