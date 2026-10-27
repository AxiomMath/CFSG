module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpSwap
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpZ

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem Rot_transpose : (Rot : Matrix (Fin 2) (Fin 2) F)ᵀ = -Rot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rot]

theorem tens_neg_left (m n : Matrix (Fin 2) (Fin 2) F) : tens (-m) n = -tens m n := by
  simp only [tens, Matrix.neg_apply, neg_smul, Matrix.fromBlocks_neg]

theorem tens_neg_right (m n : Matrix (Fin 2) (Fin 2) F) : tens m (-n) = -tens m n := by
  simp only [tens, Matrix.fromBlocks_neg, smul_neg]

theorem tens_sub_left (m m' n : Matrix (Fin 2) (Fin 2) F) :
    tens (m - m') n = tens m n - tens m' n := by
  rw [sub_eq_add_neg, tens_add_left, tens_neg_left, ← sub_eq_add_neg]

theorem transpose_gram_tens (m n : Matrix (Fin 2) (Fin 2) F) :
    (tens m n)ᵀ * gram F 2 = tens (mᵀ * J0) nᵀ := by
  rw [gram_eq_tens, tens_transpose, tens_mul, mul_one]

theorem symplectic_tens (m₀ m₁ : Matrix (Fin 2) (Fin 2) F) :
    (tens m₀ 1 + tens m₁ Rot)ᵀ * gram F 2 * (tens m₀ 1 + tens m₁ Rot) =
      tens (m₀ᵀ * J0 * m₀ + m₁ᵀ * J0 * m₁) 1 + tens (m₀ᵀ * J0 * m₁ - m₁ᵀ * J0 * m₀) Rot := by
  rw [Matrix.transpose_add, add_mul, transpose_gram_tens, transpose_gram_tens,
    Matrix.transpose_one, add_mul, mul_add, mul_add, tens_mul, tens_mul, tens_mul, tens_mul,
    mul_one, mul_one, one_mul, Rot_transpose_mul_self, Rot_transpose, tens_neg_right,
    tens_add_left, tens_sub_left]
  abel

theorem tens_zero_left (n : Matrix (Fin 2) (Fin 2) F) : tens 0 n = 0 := by
  simp [tens]

theorem exists_proportional_of_unitary (h2 : (2 : F) ≠ 0) {m₀ m₁ : Matrix (Fin 2) (Fin 2) F}
    (hA : m₀ᵀ * J0 * m₀ + m₁ᵀ * J0 * m₁ = J0) (hB : m₀ᵀ * J0 * m₁ - m₁ᵀ * J0 * m₀ = 0) :
    ∃ (μ : Matrix (Fin 2) (Fin 2) F) (a b : F), μ.det ≠ 0 ∧ m₀ = a • μ ∧ m₁ = b • μ := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, m₀ = !![a, b; c, d] :=
    ⟨m₀ 0 0, m₀ 0 1, m₀ 1 0, m₀ 1 1, Matrix.eta_fin_two m₀⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ a b c d, m₁ = !![a, b; c, d] :=
    ⟨m₁ 0 0, m₁ 0 1, m₁ 1 0, m₁ 1 1, Matrix.eta_fin_two m₁⟩
  have hA01 := congrFun (congrFun hA 0) 1
  have hB00 := congrFun (congrFun hB 0) 0
  have hB11 := congrFun (congrFun hB 1) 1
  have hB01 := congrFun (congrFun hB 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, J0] at hA01 hB00 hB11 hB01
  have r1 : a * g = c * e := by
    have : (2 : F) * (a * g - c * e) = 0 := by linear_combination hB00
    have := (mul_eq_zero.mp this).resolve_left h2
    linear_combination this
  have r2 : b * h = d * f := by
    have : (2 : F) * (b * h - d * f) = 0 := by linear_combination hB11
    have := (mul_eq_zero.mp this).resolve_left h2
    linear_combination this
  have r3 : a * h - c * f = d * e - b * g := by linear_combination hB01
  have hD : (a * d - b * c) + (e * h - f * g) = 1 := by linear_combination hA01
  have k1 : (a * d - b * c) * e = (a * h - c * f) * a := by
    linear_combination (-a) * r3 + b * r1
  have k2 : (a * d - b * c) * f = (a * h - c * f) * b := by linear_combination (-a) * r2
  have k3 : (a * d - b * c) * g = (a * h - c * f) * c := by
    linear_combination (-c) * r3 + d * r1
  have k4 : (a * d - b * c) * h = (a * h - c * f) * d := by linear_combination (-c) * r2
  have l1 : (e * h - f * g) * a = (a * h - c * f) * e := by linear_combination (-f) * r1
  have l2 : (e * h - f * g) * b = (a * h - c * f) * f := by
    linear_combination (-f) * r3 + e * r2
  have l3 : (e * h - f * g) * c = (a * h - c * f) * g := by linear_combination (-h) * r1
  have l4 : (e * h - f * g) * d = (a * h - c * f) * h := by
    linear_combination (-h) * r3 + g * r2
  by_cases hD0 : a * d - b * c = 0
  · have hD1 : e * h - f * g ≠ 0 := by
      intro h0
      rw [hD0, h0] at hD
      simp at hD
    obtain ⟨t, ht⟩ : ∃ t : F, t * (e * h - f * g) = a * h - c * f :=
      ⟨(a * h - c * f) / (e * h - f * g), div_mul_cancel₀ _ hD1⟩
    have ea : a = t * e := mul_left_cancel₀ hD1 (by linear_combination l1 - e * ht)
    have eb : b = t * f := mul_left_cancel₀ hD1 (by linear_combination l2 - f * ht)
    have ec : c = t * g := mul_left_cancel₀ hD1 (by linear_combination l3 - g * ht)
    have ed : d = t * h := mul_left_cancel₀ hD1 (by linear_combination l4 - h * ht)
    refine ⟨!![e, f; g, h], t, 1, ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      exact hD1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ea, eb, ec, ed]
    · simp
  · obtain ⟨t, ht⟩ : ∃ t : F, t * (a * d - b * c) = a * h - c * f :=
      ⟨(a * h - c * f) / (a * d - b * c), div_mul_cancel₀ _ hD0⟩
    have ee : e = t * a := mul_left_cancel₀ hD0 (by linear_combination k1 - a * ht)
    have ef : f = t * b := mul_left_cancel₀ hD0 (by linear_combination k2 - b * ht)
    have eg : g = t * c := mul_left_cancel₀ hD0 (by linear_combination k3 - c * ht)
    have eh : h = t * d := mul_left_cancel₀ hD0 (by linear_combination k4 - d * ht)
    refine ⟨!![a, b; c, d], 1, t, ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      exact hD0
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ee, ef, eg, eh]

@[expose] noncomputable def conjSL (μ : Matrix (Fin 2) (Fin 2) F) (hμ : μ.det ≠ 0)
    (h : SL(2, F)) : SL(2, F) :=
  ⟨μ * (h : Matrix (Fin 2) (Fin 2) F) * μ⁻¹, by
    rw [Matrix.det_mul, Matrix.det_mul, h.det_coe, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    field_simp⟩

theorem coe_conjSL (μ : Matrix (Fin 2) (Fin 2) F) (hμ : μ.det ≠ 0) (h : SL(2, F)) :
    (conjSL μ hμ h : Matrix (Fin 2) (Fin 2) F) = μ * (h : Matrix (Fin 2) (Fin 2) F) * μ⁻¹ := rfl

theorem exists_conj_Δsl (h2 : (2 : F) ≠ 0) {g : StatedSp 2 F} (hg : g * xSw = xSw * g)
    (h : SL(2, F)) : ∃ h' : SL(2, F), g * Δsl h = Δsl h' * g := by
  have hG : mat 2 F g * tens 1 Rot = tens 1 Rot * mat 2 F g := by
    have := congrArg (mat 2 F) hg
    rwa [map_mul, map_mul, mat_xSw] at this
  obtain ⟨m₀, m₁, hGe⟩ := exists_tens_of_commute hG
  have hsymp := mat_transpose_mul_gram_mul g
  rw [hGe, symplectic_tens, gram_eq_tens] at hsymp
  have hsymp' : tens (m₀ᵀ * J0 * m₀ + m₁ᵀ * J0 * m₁) 1 + tens (m₀ᵀ * J0 * m₁ - m₁ᵀ * J0 * m₀) Rot =
      tens J0 1 + tens 0 Rot := by
    rw [hsymp, tens_zero_left, add_zero]
  obtain ⟨hA, hB⟩ := tens_coeff hsymp'
  obtain ⟨μ, a, b, hμ, rfl, rfl⟩ := exists_proportional_of_unitary h2 hA hB
  have hGe' : mat 2 F g = tens μ (a • 1 + b • Rot) := by
    rw [hGe, tens_smul_left, tens_smul_left, tens_add_right, tens_smul_right, tens_smul_right]
  refine ⟨conjSL μ hμ h, mat_injective ?_⟩
  have hinv : μ⁻¹ * μ = 1 := Matrix.nonsing_inv_mul μ (isUnit_iff_ne_zero.mpr hμ)
  rw [map_mul, map_mul, hGe', mat_Δsl, mat_Δsl, tens_mul, tens_mul, coe_conjSL, mul_one, one_mul,
    mul_assoc (μ * (h : Matrix (Fin 2) (Fin 2) F)) μ⁻¹ μ, hinv, mul_one]

theorem normal_subgroupOf_centralizer_range_Δsl (h2 : (2 : F) ≠ 0) :
    ((Δsl (F := F)).range.subgroupOf
      (Subgroup.centralizer ({xSw} : Set (StatedSp 2 F)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨h, hh⟩ := Subgroup.mem_subgroupOf.mp hn
  have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
  obtain ⟨h', hh'⟩ := exists_conj_Δsl h2 hg h
  refine Subgroup.mem_subgroupOf.mpr ⟨h', ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hh]
  exact (mul_inv_eq_iff_eq_mul.mpr hh').symm

theorem isComponentOf_range_Δsl [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    CFSG.Open.IsComponentOf (Δsl (F := F)).range
      (fixedGroup (MulAut.conj (xSw : StatedSp 2 F))) := by
  rw [fixedGroup_conj_eq]
  have hle : (Δsl (F := F)).range ≤ Subgroup.centralizer ({xSw} : Set (StatedSp 2 F)) := by
    rintro _ ⟨h, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Δsl_commute_xSw h)
  exact ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle
    (normal_subgroupOf_centralizer_range_Δsl h2), isQuasisimple_range_Δsl h4⟩

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
