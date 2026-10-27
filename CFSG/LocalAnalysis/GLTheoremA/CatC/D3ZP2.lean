module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL7
public import CFSG.RankThree.PartOne.U5K.Hyp.SLTwo

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Mat

variable {K : Type} [Field K] [Finite K]

@[expose] def gmat (a : Kˣ) (A : SL2 K) : Matrix (Fin 2) (Fin 2) K :=
  !![(a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 0, (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 1;
    (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1]

@[expose] def col0 (e : SL2 K) : Fin 2 → K :=
  ![(e : Matrix (Fin 2) (Fin 2) K) 0 0, (e : Matrix (Fin 2) (Fin 2) K) 1 0]

theorem col0_ne_zero (e : SL2 K) : col0 e ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [col0, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have hdet := det_SL2 e
  rw [h0, h1] at hdet
  simp at hdet

theorem gmat_mulVec_zero (a : Kˣ) (A e : SL2 K) :
    (gmat a A *ᵥ col0 e) 0 = (a : K) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (e : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (e : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  simp [gmat, col0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem gmat_mulVec_one (a : Kˣ) (A e : SL2 K) :
    (gmat a A *ᵥ col0 e) 1 = (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (e : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (e : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [gmat, col0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem X10_eq (a : Kˣ) (A e : SL2 K) :
    ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (e : Matrix (Fin 2) (Fin 2) K) 0 0 * (gmat a A *ᵥ col0 e) 1 -
        (e : Matrix (Fin 2) (Fin 2) K) 1 0 * (gmat a A *ᵥ col0 e) 0 := by
  rw [coe_X10, gmat_mulVec_zero, gmat_mulVec_one]

theorem eigen_of_X10 (a : Kˣ) (A e : SL2 K)
    (h : ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ l : K, gmat a A *ᵥ col0 e = l • col0 e := by
  rw [X10_eq] at h
  set w := gmat a A *ᵥ col0 e with hw
  have hv := col0_ne_zero e
  have hv0 : col0 e 0 = (e : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
  have hv1 : col0 e 1 = (e : Matrix (Fin 2) (Fin 2) K) 1 0 := rfl
  by_cases h0 : (e : Matrix (Fin 2) (Fin 2) K) 0 0 = 0
  · have h1 : (e : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hw0 : w 0 = 0 := by
      have : (e : Matrix (Fin 2) (Fin 2) K) 1 0 * w 0 = 0 := by
        rw [h0] at h; linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left h1
    refine ⟨w 1 / (e : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    funext i
    fin_cases i
    · simp [hw0, hv0, h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [hv1]; field_simp
  · refine ⟨w 0 / (e : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [hv0]; field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      rw [hv1]
      field_simp
      linear_combination h

theorem X10_of_eigen (a : Kˣ) (A e : SL2 K) {l : K} (h : gmat a A *ᵥ col0 e = l • col0 e) :
    ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [X10_eq]
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have e0 : (col0 e) 0 = (e : Matrix (Fin 2) (Fin 2) K) 0 0 := rfl
  have e1 : (col0 e) 1 = (e : Matrix (Fin 2) (Fin 2) K) 1 0 := rfl
  rw [e0] at h0
  rw [e1] at h1
  rw [h0, h1]; ring

theorem gmat_comm (a a' : Kˣ) (A A' : SL2 K) (h : dconj a'⁻¹ A * A' = dconj a⁻¹ A' * A) :
    gmat a A * gmat a' A' = gmat a' A' * gmat a A := by
  have e00 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have e01 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 1) h
  have e10 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 1 0) h
  have e11 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 1 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dconj, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, inv_inv, Units.val_inv_eq_inv_val] at e00 e01 e10 e11
  have ha : (a : K) ≠ 0 := a.ne_zero
  have ha' : (a' : K) ≠ 0 := a'.ne_zero
  field_simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination e11

theorem common_eigen {M N : Matrix (Fin 2) (Fin 2) K} (hMN : M * N = N * M) {v v' : Fin 2 → K}
    (hv : v ≠ 0) (hv' : v' ≠ 0) {l l' : K} (hl : M *ᵥ v = l • v) (hl' : N *ᵥ v' = l' • v') :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ (∃ μ : K, M *ᵥ w = μ • w) ∧ ∃ μ' : K, N *ᵥ w = μ' • w := by
  by_cases hsc : ∃ c : K, M = c • 1
  · obtain ⟨c, hc⟩ := hsc
    refine ⟨v', hv', ⟨c, by rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]⟩, l', hl'⟩
  · push Not at hsc
    obtain ⟨μ, hμ⟩ := CFSG.RankThree.PartOne.U5K.Hyp.exists_eigen_of_commute M N l v hv hl hMN hsc
    exact ⟨v, hv, ⟨l, hl⟩, μ, hμ⟩

end Mat

end CFSG.LocalAnalysis.GLTheoremA
