module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM17

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem conjSp_eq_self_of_comm (M : gsp 2 F) (y : StatedSp 2 F)
    (h : gm M * mat 2 F y = mat 2 F y * gm M) : conjSp 2 F M y = y := by
  apply Subtype.ext
  rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact h

theorem card_ineq (q : ℕ) (hq : 2 ≤ q) :
    (q * (q ^ 2 - 1)) ^ 2 < 2 * (q * q * ((q * q) ^ 2 - 1)) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (q * q) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h3 : (0 : ℤ) < (q : ℤ) ^ 2 * ((q : ℤ) ^ 4 + 2 * (q : ℤ) ^ 2 - 3) := by
    have : (0 : ℤ) < (q : ℤ) ^ 4 + 2 * (q : ℤ) ^ 2 - 3 := by nlinarith
    positivity
  nlinarith [h3]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem hasBigFix_of_plus [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (β : Y ≃* Y) (M : gsp 2 F)
    (hβ : ∀ x, β (fr.ψ x) = fr.ψ (conjSp 2 F M x)) (hns : ¬ IsSquare (mu M))
    (hN : gm M * gm M = mu M • 1) :
    ∃ L : Subgroup Y, (∀ x ∈ L, β x = x) ∧ IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Nat.card SL(2, F) ^ 2 < 4 * Nat.card L := by
  obtain ⟨g, hg⟩ := exists_conj_nPlus h2 hN hns
  have : Fact (¬ IsSquare (mu M)) := ⟨hns⟩
  set φ := fr.ψ.comp (MulAut.conj g).toMonoidHom with hφdef
  have hφ : φ.ker = spScalars 2 F := ker_comp_conj fr.ψ fr.ker g
  refine ⟨(φ.comp (phiSL (mu M))).range, ?_, isSimpleGroup_range_phiSL _ h4 φ hφ,
    exists_not_comm_range_phiSL _ h2 φ hφ, ?_⟩
  · rintro _ ⟨s, rfl⟩
    change β (fr.ψ (g * phiSL (mu M) s * g⁻¹)) = fr.ψ (g * phiSL (mu M) s * g⁻¹)
    rw [hβ, conjSp_eq_self_of_comm]
    have hGi : mat 2 F g * mat 2 F g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hiG : ∀ X, mat 2 F g⁻¹ * (mat 2 F g * X) = X := fun X => by
      rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    have hM : gm M = mat 2 F g * nPlus (mu M) * mat 2 F g⁻¹ := by
      rw [hg, Matrix.mul_assoc, hGi, Matrix.mul_one]
    rw [map_mul, map_mul, mat_phiSL, hM]
    simp only [Matrix.mul_assoc, hiG]
    rw [← Matrix.mul_assoc (nPlus (mu M)), ← phiM_mul_nPlus, Matrix.mul_assoc]
  · have : Finite (QuadraticAlgebra F (mu M) 0) := finite_quadAlg _
    have hc := card_range_phiSL (mu M) hodd φ hφ
    rw [natCard_sl2, card_quadAlg] at hc
    rw [natCard_sl2]
    have hq : 2 ≤ Nat.card F := by omega
    have := card_ineq (Nat.card F) hq
    omega

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
