module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ADefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74AConj

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section SL2

variable {K : Type*} [Field K] [Finite K]

theorem sl2_trace_eq_two_of_pow_ringChar {M : SL(2, K)} (hM : M ^ ringChar K = 1) :
    M 0 0 + M 1 1 = 2 := by
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hA : ((M : Matrix (Fin 2) (Fin 2) K) - 1) ^ ringChar K = 0 := by
    rw [sub_pow_char_of_commute (R := Matrix (Fin 2) (Fin 2) K) (p := ringChar K)
      (Commute.one_right _), one_pow, ← Matrix.SpecialLinearGroup.coe_pow, hM,
      Matrix.SpecialLinearGroup.coe_one, sub_self]
  have hd : ((M : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 := by
    have h := congrArg Matrix.det hA
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact (pow_eq_zero_iff hp.out.ne_zero).mp h
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hd hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hd
  linear_combination hdet - hd

theorem sl2_exists_conj_upperSL2 {M : SL(2, K)} (hM1 : M ≠ 1) (hMp : M ^ ringChar K = 1) :
    ∃ N : SL(2, K), ∃ c : K, c ≠ 0 ∧ N * M * N⁻¹ = upperSL2 c := by
  have htr := sl2_trace_eq_two_of_pow_ringChar hMp
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.det_coe
    rwa [Matrix.det_fin_two] at h
  by_cases hc : M 1 0 = 0
  · rw [hc, mul_zero, sub_zero] at hdet
    have h00 : M 0 0 = 1 := by
      have h : (M 0 0 - 1) * (M 0 0 - 1) = 0 := by linear_combination M 0 0 * htr - hdet
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
    have h11 : M 1 1 = 1 := by linear_combination htr - h00
    refine ⟨1, M 0 1, fun h0 => hM1 ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h11, hc, h0]
    · rw [one_mul, inv_one, mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h11, hc]
  · let N : SL(2, K) := ⟨!![0, (M 1 0)⁻¹; -M 1 0, M 0 0 - 1], by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring⟩
    have hNM : N * M = upperSL2 (-(M 1 0)⁻¹) * N := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2]
      show !![0, (M 1 0)⁻¹; -M 1 0, M 0 0 - 1] * (M : Matrix (Fin 2) (Fin 2) K) =
        !![1, -(M 1 0)⁻¹; 0, 1] * !![0, (M 1 0)⁻¹; -M 1 0, M 0 0 - 1]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (M 1 0)⁻¹ * htr
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination hdet - htr
    exact ⟨N, -(M 1 0)⁻¹, neg_ne_zero.mpr (inv_ne_zero hc), by rw [hNM, mul_inv_cancel_right]⟩

theorem exists_conj_upperSL2_of_mem_range {G : Type*} [Group G] (ρ : SL(2, K) →* G)
    (hρ : Function.Injective ρ) {y : G} (hy : y ∈ ρ.range) (hy1 : y ≠ 1)
    (hyp : y ^ ringChar K = 1) :
    ∃ g ∈ ρ.range, ∃ c : K, c ≠ 0 ∧ g * y * g⁻¹ = ρ (upperSL2 c) := by
  obtain ⟨M, rfl⟩ := hy
  have hM1 : M ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hMp : M ^ ringChar K = 1 := hρ (by rw [map_pow, hyp, map_one])
  obtain ⟨N, c, hc, hN⟩ := sl2_exists_conj_upperSL2 hM1 hMp
  exact ⟨ρ N, ⟨N, rfl⟩, c, hc, by rw [← map_inv, ← map_mul, ← map_mul, hN]⟩

end SL2

section Torus

variable (K : Type) [Field K]

theorem tSeven_eq_longTorus :
    tSeven K = (oddFrame 3 K).toHypFrame.longTorus fin3_zero_ne_one true true (-1) := by
  rw [HypFrame.longTorus_apply]
  show (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (-1) = _
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL2]

theorem longTorus_zero_two_mem_centralizer (τ : Kˣ) :
    (oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true τ ∈
      centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
  rw [mem_centralizer_singleton_iff, tSeven_eq_longTorus]
  exact ((oddFrame 3 K).toHypFrame.commute_longTorus_longTorus _ true true τ fin3_zero_ne_one
    true true (-1)).eq

variable {K}

theorem longTorus_conj_shortSeven_upperSL2 {c : K} (hc : c ≠ 0) :
    (oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
        (Units.mk0 c hc)⁻¹ * shortSeven K (upperSL2 c) *
      ((oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
        (Units.mk0 c hc)⁻¹)⁻¹ = qThree K := by
  have he : longCoroot (0 : Fin 3) 2 true true 2 true = 1 := by decide
  show _ = (oddFrame 3 K).shortSL2 2 true (upperSL2 1)
  rw [OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_upperSL2,
    OddFrame.longTorus_conj_shortRoot, he, zpow_one, Units.val_inv_eq_inv_val, Units.val_mk0,
    inv_mul_cancel₀ hc]

theorem longTorus_conj_longSL2_upperSL2 {c : K} (hc : c ≠ 0) :
    (oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
        (Units.mk0 c hc)⁻¹ *
        (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 c) *
      ((oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
        (Units.mk0 c hc)⁻¹)⁻¹ = qOne K := by
  have he : longCoroot (0 : Fin 3) 2 true true 0 true + longCoroot (0 : Fin 3) 2 true true 1 true =
      1 := by decide
  show _ = (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 1)
  rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2, HypFrame.longTorus_conj_longRoot, he,
    zpow_one, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hc]

end Torus

theorem a3_holds : A3 := by
  intro K _ _ hodd
  have hinj₂ := longSL2_injective (oddFrame 3 K).toHypFrame fin3_zero_ne_one true true
  have hc₁ : ∀ y ∈ spinJ₁ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g ∈ spinJ₁ K, ∃ c : K, c ≠ 0 ∧ g * y * g⁻¹ = shortSeven K (upperSL2 c) :=
    fun y hy hy1 hyp => exists_conj_upperSL2_of_mem_range _
      (LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true) hy hy1 hyp
  have hc₂ : ∀ y ∈ spinJ₂ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g ∈ spinJ₂ K, ∃ c : K, c ≠ 0 ∧ g * y * g⁻¹ =
        (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 c) :=
    fun y hy hy1 hyp => exists_conj_upperSL2_of_mem_range _ hinj₂ hy hy1 hyp
  have hb₂ : ∀ y ∈ spinJ₂ K, y ≠ 1 → y ^ ringChar K = 1 →
      ∃ g : spinGroup (quadOdd 3 K), g * y * g⁻¹ = qOne K := by
    intro y hy hy1 hyp
    obtain ⟨g, -, c, hc, hg⟩ := hc₂ y hy hy1 hyp
    refine ⟨(oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
      (Units.mk0 c hc)⁻¹ * g, ?_⟩
    rw [← longTorus_conj_longSL2_upperSL2 hc, ← hg]
    group
  refine ⟨fun y hy hy1 hyp => ?_, ?_, hc₁, hc₂⟩
  · obtain ⟨g, ⟨M, rfl⟩, c, hc, hg⟩ := hc₁ y hy hy1 hyp
    refine ⟨(oddFrame 3 K).toHypFrame.longTorus (show (0 : Fin 3) ≠ 2 by decide) true true
      (Units.mk0 c hc)⁻¹ * shortSeven K M,
      mul_mem (longTorus_zero_two_mem_centralizer K _)
        (mem_centralizer_singleton_iff.mpr (commute_shortSeven_longSL2 true M (-1)).eq), ?_⟩
    rw [← longTorus_conj_shortSeven_upperSL2 hc, ← hg]
    group
  · rintro y (hy | hy) hy1 hyp
    · exact hb₂ y hy hy1 hyp
    · have hy' : iBar K * y * (iBar K)⁻¹ ∈ spinJ₂ K := by
        rw [← map_conj_iBar_spinJ₃ K]
        exact ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      obtain ⟨g, hg⟩ := hb₂ _ hy' (fun h => hy1 (conj_eq_one_iff.mp h))
        (by rw [conj_pow, hyp, mul_one, mul_inv_cancel])
      exact ⟨g * iBar K, by rw [← hg]; group⟩

end CFSG.ComponentClassification.HarrisLit.T1.S74
