module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Mat2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3 CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

theorem entries_of_rho1_eq_neg_one {g : (P1 : Subgroup (SL3 F))} (hg : rho1 g = -1) :
    (g : SL3 F).1 0 0 = 1 ∧ (g : SL3 F).1 1 0 = 0 ∧ (g : SL3 F).1 2 0 = 0 ∧
      (g : SL3 F).1 1 1 = -1 ∧ (g : SL3 F).1 1 2 = 0 ∧ (g : SL3 F).1 2 1 = 0 ∧
      (g : SL3 F).1 2 2 = -1 := by
  obtain ⟨h1, h2⟩ := g.2
  have hb : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ = -1 := by
    have := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hg
    simpa [coe_rho1] using this
  have e11 := congrFun (congrFun hb 0) 0
  have e12 := congrFun (congrFun hb 0) 1
  have e21 := congrFun (congrFun hb 1) 0
  have e22 := congrFun (congrFun hb 1) 1
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e11 e12 e21 e22
  simp at e11 e12 e21 e22
  have hdet := P1_det_eq g.2
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hdet
  rw [e11, e12, e21, e22] at hdet
  refine ⟨?_, h1, h2, e11, e12, e21, e22⟩
  simpa using hdet

@[expose] def NegShape (z : SL3 F) : Prop :=
  z.1 0 0 = 1 ∧ z.1 1 0 = 0 ∧ z.1 2 0 = 0 ∧ z.1 1 1 = -1 ∧ z.1 1 2 = 0 ∧ z.1 2 1 = 0 ∧ z.1 2 2 = -1

theorem mem_P1_of_comm (h2 : (2 : F) ≠ 0) {z n : SL3 F} (hz : NegShape z) (hc : n * z = z * n) :
    n ∈ (P1 : Subgroup (SL3 F)) := by
  obtain ⟨z00, z10, z20, z11, z12, z21, z22⟩ := hz
  have hze : (z : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = e0 := by
    rw [mulVec_e0]
    funext i
    fin_cases i <;> simp [z00, z10, z20, Pi.single_apply]
  have hfix : (z : Matrix (Fin 3) (Fin 3) F) *ᵥ ((n : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) =
      (n : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 := by
    rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, ← hc, SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, hze]
  rw [mulVec_e0] at hfix
  have a1 : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    have h1 := congrFun hfix 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, z10, z11, z12] at h1
    linear_combination -h1
  have a2 : (2 : F) * (n : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    have h1 := congrFun hfix 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, z20, z21, z22] at h1
    linear_combination -h1
  exact ⟨(mul_eq_zero.mp a1).resolve_left h2, (mul_eq_zero.mp a2).resolve_left h2⟩

theorem eq_one_of_mem_Q1_of_comm (h2 : (2 : F) ≠ 0) {z m : SL3 F} (hz : NegShape z)
    (hm : m ∈ (Q1 : Subgroup (SL3 F))) (hc : m * z = z * m) : m = 1 := by
  obtain ⟨z00, z10, z20, z11, z12, z21, z22⟩ := hz
  obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp hm
  have hφ0 : φ 0 = 0 := by simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using hφ
  have hcm := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [SpecialLinearGroup.coe_mul, coe_tv hφ] at hcm
  have e1 := congrFun (congrFun hcm 0) 1
  have e2 := congrFun (congrFun hcm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_mul, Matrix.mul_add,
    Matrix.vecMulVec_apply, Pi.single_apply, hφ0, z00, z10, z20, z11, z12, z21, z22] at e1 e2
  have a1 : (2 : F) * φ 1 = 0 := by linear_combination -e1
  have a2 : (2 : F) * φ 2 = 0 := by linear_combination -e2
  have hφ1 := (mul_eq_zero.mp a1).resolve_left h2
  have hφ2 := (mul_eq_zero.mp a2).resolve_left h2
  have : φ = 0 := by
    funext i
    fin_cases i <;> simp [hφ0, hφ1, hφ2]
  rw [this, tv_zero_right]

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
