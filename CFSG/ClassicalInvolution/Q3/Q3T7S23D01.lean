module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1S
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.RouteD.SU4Pattern
open scoped MatrixGroups

theorem comm_blockDiag_of_map_centralizes {X : Type} [Group X]
    (ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (hcop : ∀ n ∈ ψ.ker, ¬ 3 ∣ orderOf n)
    (h0 : Q3W.Pow3 (rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4)))
    (h2 : Q3W.Pow3 rootSU2Two) (x : Su (GaloisField 3 (2 * 1)) 3 1 4)
    (hx0 : ∀ b ∈ rootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4),
      ψ x * ψ b = ψ b * ψ x)
    (hx2 : ∀ b ∈ rootSU2Two, ψ x * ψ b = ψ b * ψ x)
    (y : Su (GaloisField 3 (2 * 1)) 3 1 4) (H₁ H₂ : Matrix (Fin 2) (Fin 2) (GaloisField 3 (2 * 1)))
    (hy : suMat y = BD H₁ H₂) : ψ x * ψ y = ψ y * ψ x := by
  have hc : ∀ {R : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)}, Q3W.Pow3 R →
      (∀ b ∈ R, ψ x * ψ b = ψ b * ψ x) → ∀ b ∈ R, x * b = b * x := by
    intro R hR hxR b hb
    refine Q3W.commutes_of_map_commute_exponent3 ψ hker hcop (A := Subgroup.zpowers x) (L := R) hR
      ?_ x (Subgroup.mem_zpowers x) b hb
    intro a ha l hl
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (ψ x) (ψ l) from hxR l hl) m).eq
  have hx0' := hc h0 hx0
  have hx2' := hc h2 hx2
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hq3 : 3 ^ 1 % 4 = 3 := by norm_num
  have hM : ∀ b : Su (GaloisField 3 (2 * 1)) 3 1 2,
      suMat x * blockMat 4 0 (suMat b) = blockMat 4 0 (suMat b) * suMat x := by
    intro b
    have h := congrArg suMat (hx0' (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) b)
      ⟨b, rfl⟩)
    rwa [suMat_mul, suMat_mul, suMat_blockEmb] at h
  obtain ⟨c, D, hcD⟩ := commutant_blockZero hK (by norm_num) hq3 hM
  have hD : ∀ b : Su (GaloisField 3 (2 * 1)) 3 1 2, D * suMat b = suMat b * D := by
    intro b
    have h := congrArg suMat (hx2' (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num) b)
      ⟨b, rfl⟩)
    rw [suMat_mul, suMat_mul, hcD, suMat_blockEmb, blockMat_two_eq_BD, BD_mul, BD_mul] at h
    simpa using (BD_inj h).2
  obtain ⟨d, hd⟩ := su2_commutant_scalar hK (by norm_num) hq3 hD
  have hxy : x * y = y * x := by
    apply suMat_injective
    rw [suMat_mul, suMat_mul, hcD, hy, hd, BD_mul, BD_mul]
    congr 1
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [← map_mul, ← map_mul, hxy]

end CFSG.ClassicalInvolution.Q3.Q3P21
