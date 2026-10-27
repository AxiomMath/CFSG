module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthArith

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix

variable {K : Type} [Field K] {d : ℕ}

@[expose] def avgMat (G : Subgroup (GL (Fin d) K)) [Fintype G] : Matrix (Fin d) (Fin d) K :=
  (Fintype.card G : K)⁻¹ • ∑ g : G, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)

@[expose] def avgSign (G : Subgroup (GL (Fin d) K)) [Fintype G] : Matrix (Fin d) (Fin d) K :=
  (2 : K) • avgMat G - 1

variable {G : Subgroup (GL (Fin d) K)} [Fintype G]

theorem mul_sum_group {g : GL (Fin d) K} (hg : g ∈ G) :
    (g : Matrix (Fin d) (Fin d) K) * ∑ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ∑ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  rw [Matrix.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : G)) _ _ fun h => by
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul]

theorem sum_group_mul {g : GL (Fin d) K} (hg : g ∈ G) :
    (∑ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) * (g : Matrix (Fin d) (Fin d) K) =
      ∑ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  rw [Matrix.sum_mul]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : G)) _ _ fun h => by
    rw [Equiv.coe_mulRight, Subgroup.coe_mul, Units.val_mul]

theorem sum_group_inv :
    ∑ h : G, (((h : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ∑ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  Fintype.sum_equiv (Equiv.inv G) _ _ fun h => by rw [Equiv.inv_apply, Subgroup.coe_inv]

theorem mul_avgMat {g : GL (Fin d) K} (hg : g ∈ G) :
    (g : Matrix (Fin d) (Fin d) K) * avgMat G = avgMat G := by
  rw [avgMat, Matrix.mul_smul, mul_sum_group hg]

theorem avgMat_mul {g : GL (Fin d) K} (hg : g ∈ G) :
    avgMat G * (g : Matrix (Fin d) (Fin d) K) = avgMat G := by
  rw [avgMat, Matrix.smul_mul, sum_group_mul hg]

theorem avgMat_mul_self (hG : (Fintype.card G : K) ≠ 0) : avgMat G * avgMat G = avgMat G := by
  calc avgMat G * avgMat G = (Fintype.card G : K)⁻¹ •
        ∑ g : G, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * avgMat G := by
        rw [← Matrix.sum_mul, ← Matrix.smul_mul]
        rfl
    _ = (Fintype.card G : K)⁻¹ • ∑ _g : G, avgMat G := by
        rw [Finset.sum_congr rfl fun h _ => mul_avgMat h.2]
    _ = avgMat G := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul,
          inv_mul_cancel₀ hG, one_smul]

theorem transpose_avgMat_mul {R : Matrix (Fin d) (Fin d) K}
    (hG : ∀ g ∈ G, ((g : Matrix (Fin d) (Fin d) K))ᵀ * R * g = R) :
    (avgMat G)ᵀ * R = R * avgMat G := by
  have hgR : ∀ h : G, ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * R =
      R * (((h : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro h
    calc ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * R =
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * R *
          ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (((h : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.mul_assoc _ ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), ← Units.val_mul,
            mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = R * (((h : GL (Fin d) K)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [hG _ h.2]
  rw [avgMat, Matrix.transpose_smul, Matrix.transpose_sum, Matrix.smul_mul, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  simp_rw [hgR]
  rw [← Matrix.mul_sum, ← Matrix.mul_sum, sum_group_inv]

theorem avgSign_mul_self (hG : (Fintype.card G : K) ≠ 0) : avgSign G * avgSign G = 1 := by
  have hP := avgMat_mul_self hG
  rw [avgSign, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    hP, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, smul_smul]
  module

theorem transpose_avgSign_mul (hGc : (Fintype.card G : K) ≠ 0) {R : Matrix (Fin d) (Fin d) K}
    (hG : ∀ g ∈ G, ((g : Matrix (Fin d) (Fin d) K))ᵀ * R * g = R) :
    (avgSign G)ᵀ * R * avgSign G = R := by
  have hP := avgMat_mul_self hGc
  have hT := transpose_avgMat_mul hG
  rw [avgSign, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.sub_mul,
    Matrix.smul_mul, hT, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, hP, Matrix.mul_one,
    Matrix.mul_one, smul_smul]
  module

theorem mul_avgMat_comm {X : Matrix (Fin d) (Fin d) K}
    (hX : ∀ g ∈ G, X * (g : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) * X) :
    X * avgMat G = avgMat G * X := by
  rw [avgMat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun h _ => hX _ h.2

theorem mul_one_sub_avgMat (hGc : (Fintype.card G : K) ≠ 0) {X : Matrix (Fin d) (Fin d) K}
    (hX : ∀ g ∈ G, X * ((g : Matrix (Fin d) (Fin d) K) - 1) = (g : Matrix (Fin d) (Fin d) K) - 1) :
    X * (1 - avgMat G) = 1 - avgMat G := by
  have hXg : ∀ h : G, X * ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 + X := by
    intro h
    have e := hX _ h.2
    rw [Matrix.mul_sub, Matrix.mul_one] at e
    rw [← e]
    abel
  have hXP : X * avgMat G = avgMat G - 1 + X := by
    rw [avgMat, Matrix.mul_smul, Matrix.mul_sum]
    simp_rw [hXg]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K, smul_add,
      smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hGc, one_smul, one_smul]
  rw [Matrix.mul_sub, Matrix.mul_one, hXP]
  abel

theorem one_sub_avgMat_mul {g : GL (Fin d) K} (hg : g ∈ G) :
    (1 - avgMat G) * ((g : Matrix (Fin d) (Fin d) K) - 1) = (g : Matrix (Fin d) (Fin d) K) - 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, avgMat_mul hg, Matrix.mul_one]
  abel

end CFSG.ComponentClassification.GSThmB.QPUCl
