module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_la_proj {K : Type} [Field K] (hK : (2 : K) ≠ 0) {n : ℕ} (hn : 4 < n)
    (U : Matrix (Fin n) (Fin 4) K) (Φ : Matrix (Fin 4) (Fin n) K) (h : Φ * U = 1) :
    (1 - (2 : K) • (U * Φ)) * (1 - (2 : K) • (U * Φ)) = 1 ∧
      (1 - (2 : K) • (U * Φ)).det = 1 ∧
      ∀ c : K, (1 - (2 : K) • (U * Φ)) ≠ c • (1 : Matrix (Fin n) (Fin n) K) := by
  set P : Matrix (Fin n) (Fin n) K := U * Φ with hP
  set A : Matrix (Fin n) (Fin n) K := (2 : K) • P with hA
  have hP2 : P * P = P := by
    rw [hP, Matrix.mul_assoc U Φ (U * Φ), ← Matrix.mul_assoc Φ U Φ, h, Matrix.one_mul]
  have hAA : A * A = (2 : K) • A := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul, hP2]
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hAA]
    rw [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub, sub_neg_eq_add, sub_add_cancel]
  ·
    rw [hA, hP]
    rw [show (2 : K) • (U * Φ) = ((2 : K) • U) * Φ from (Matrix.smul_mul (2 : K) U Φ).symm]
    rw [Matrix.det_one_sub_mul_comm, Matrix.mul_smul, h]
    rw [show (1 : Matrix (Fin 4) (Fin 4) K) - (2 : K) • (1 : Matrix (Fin 4) (Fin 4) K) =
        (-1 : K) • (1 : Matrix (Fin 4) (Fin 4) K) from by
      rw [neg_one_smul, two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]]
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    ring
  ·
    intro c hc
    rw [hA] at hc
    have hL : Φ * (1 - (2 : K) • P) * U =
        (1 : Matrix (Fin 4) (Fin 4) K) - (2 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul]
      rw [h, hP]
      have hinner : Φ * (U * Φ) * U = (1 : Matrix (Fin 4) (Fin 4) K) := by
        rw [← Matrix.mul_assoc Φ U Φ, h, Matrix.one_mul, h]
      rw [hinner]
    have hR : Φ * (c • (1 : Matrix (Fin n) (Fin n) K)) * U =
        c • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]
    have hcM : c • (1 : Matrix (Fin 4) (Fin 4) K) =
        (1 : Matrix (Fin 4) (Fin 4) K) - (2 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [← hR, ← hL]
      exact (congrArg (fun M => Φ * M * U) hc).symm
    have hc_eq : c = -1 := by
      have h00 := congrFun (congrFun hcM 0) 0
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq, mul_one,
        smul_eq_mul] at h00
      rw [show (1 : K) - 2 = -1 by ring] at h00
      exact h00
    have hP1 : P = 1 := by
      have hneg : (1 : Matrix (Fin n) (Fin n) K) - (2 : K) • P =
          -(1 : Matrix (Fin n) (Fin n) K) := by
        rw [hc, hc_eq, neg_one_smul]
      have h1 : (1 : Matrix (Fin n) (Fin n) K) =
          -(1 : Matrix (Fin n) (Fin n) K) + (2 : K) • P :=
        (sub_eq_iff_eq_add).mp hneg
      have h4 : (1 : Matrix (Fin n) (Fin n) K) + 1 = (2 : K) • P :=
        (eq_neg_add_iff_add_eq).mp h1
      have h2 : (2 : K) • P = (2 : K) • (1 : Matrix (Fin n) (Fin n) K) :=
        h4.symm.trans (two_smul K (1 : Matrix (Fin n) (Fin n) K)).symm
      have := congrArg (fun M => (2 : K)⁻¹ • M) h2
      simpa [smul_smul, inv_mul_cancel₀ hK] using this
    have hrank1 : (U * Φ).rank = n := by
      rw [← hP, hP1, Matrix.rank_one, Fintype.card_fin]
    have hrank2 : (U * Φ).rank ≤ 4 := by
      calc (U * Φ).rank ≤ Φ.rank := Matrix.rank_mul_le_right U Φ
        _ ≤ Fintype.card (Fin 4) := Matrix.rank_le_card_height Φ
        _ = 4 := Fintype.card_fin 4
    exact absurd (hrank1 ▸ hrank2) (not_le.mpr hn)

end CFSG.OddStandard.HigherRank.YamadaG23
