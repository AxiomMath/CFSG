module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmallModel
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverRootData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

theorem card_psu3Model_one : Nat.card (PSU3Model 1) = 72 := by
  let k := GaloisField 2 1
  let E := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian 1 (by norm_num)
  have hcard : Nat.card E = (2 ^ 1) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 1 (by norm_num)]
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ 1 :=
    quadraticBinaryFrobenius_fixed_card 1 (by norm_num)
  obtain ⟨u⟩ := projectiveSpecialUnitary_equiv_model_of_pos J 1 le_rfl rfl hcard hfixed _ rfl
  rw [← Nat.card_congr u.toEquiv,
    CFSG.ShultStronglyClosedTI.unitaryCover_native_card J 2 hcard hfixed rfl]
  decide

theorem card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have h := Polynomial.SplittingField.adjoin_rootSet
    (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2))
  have hpoly : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)) = 0 := by simp
  have hempty : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : Polynomial (ZMod 2)).rootSet
      (GaloisField 2 0) = ∅ := by
    ext x
    simp only [Polynomial.mem_rootSet, hpoly, ne_eq, not_true_eq_false, false_and,
      Set.mem_empty_iff_false]
  change Algebra.adjoin (ZMod 2) ((Polynomial.X ^ 2 ^ 0 - Polynomial.X :
    Polynomial (ZMod 2)).rootSet (GaloisField 2 0)) = ⊤ at h
  rw [hempty, Algebra.adjoin_empty] at h
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := by
    intro x
    have : x ∈ (⊥ : Subalgebra (ZMod 2) (GaloisField 2 0)) := by rw [h]; trivial
    exact Algebra.mem_bot.mp this
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) (GaloisField 2 0)).injective,
    hsurj⟩), Nat.card_zmod]

variable {F : Type} [Field F]

@[expose] def middleFixed (F : Type) [Field F] : Subgroup (GL (Fin 3) F) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro A B ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    rw [a1, a2, a3, a4, a5, b1, b2, b3, b4, b5]
    simp
  inv_mem' := by
    rintro A ⟨a1, a2, a3, a4, a5⟩
    have h1 : (A : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e10 := congrFun (congrFun h1 1) 0
    have e11 := congrFun (congrFun h1 1) 1
    have e12 := congrFun (congrFun h1 1) 2
    have e01 := congrFun (congrFun h2 0) 1
    have e21 := congrFun (congrFun h2 2) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5] at e10 e11 e12 e01 e21
    exact ⟨by simpa using e10, by simpa using e11, by simpa using e12, by simpa using e01,
      by simpa using e21⟩


theorem mem_middleFixed_of_isometry [CharP F 2] (A : GL (Fin 3) F)
    (hA : (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) F) j i ^ (2 ^ 0)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] * (A : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hdet : GeneralLinearGroup.det A = 1) : A ∈ middleFixed F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet1 : (A : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet
  show (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
  generalize (A : Matrix (Fin 3) (Fin 3) F) = a at hA hdet1 ⊢
  have e : ∀ i j, a 2 i * a 0 j + a 1 i * a 1 j + a 0 i * a 2 j =
      (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    rw [← congrFun (congrFun hA i) j]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, pow_zero, pow_one]
    simp
  have e00 := e 0 0
  have e22 := e 2 2
  have e11 := e 1 1
  have e01 := e 0 1
  have e21 := e 2 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const] at e00 e22 e11 e01 e21
  have h10 : a 1 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linear_combination e00 - a 2 0 * a 0 0 * h2)
  have h12 : a 1 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linear_combination e22 - a 2 2 * a 0 2 * h2)
  have h11 : a 1 1 = 1 := by
    have : (a 1 1 - 1) ^ 2 = 0 := by
      linear_combination e11 + (1 - a 1 1 - a 0 1 * a 2 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hdet' : a 0 0 * a 2 2 - a 0 2 * a 2 0 = 1 := by
    rw [Matrix.det_fin_three, h10, h12, h11] at hdet1
    linear_combination hdet1
  rw [h10, h11] at e01
  rw [h12, h11] at e21
  refine ⟨h10, h11, h12, ?_, ?_⟩
  · linear_combination (-a 0 1) * hdet' + a 0 0 * e21 - a 0 2 * e01
  · linear_combination (-a 2 1) * hdet' + a 2 2 * e01 - a 2 0 * e21


theorem middleFixed_injective :
    Function.Injective (fun A : middleFixed F =>
      (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0,
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2,
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0,
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2)) := by
  rintro ⟨A, a1, a2, a3, a4, a5⟩ ⟨B, b1, b2, b3, b4, b5⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h00, h02, h20, h22⟩ := h
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  fin_cases i <;> fin_cases j <;> simp_all

theorem card_psu3Model_zero_le : Nat.card (PSU3Model 0) ≤ 16 := by
  have hF : Nat.card (GaloisField 2 (2 * 0)) = 2 := card_galoisField_two_zero
  have : Finite (GaloisField 2 (2 * 0)) := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  set U := {A : GL (Fin 3) (GaloisField 2 (2 * 0)) |
      (Matrix.of fun i j =>
          (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 0))) j i ^ (2 ^ 0)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 0))) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    GeneralLinearGroup.det A = 1} with hU
  have hle : Subgroup.closure U ≤ middleFixed (GaloisField 2 (2 * 0)) :=
    (Subgroup.closure_le _).mpr fun A hA => mem_middleFixed_of_isometry A hA.1 hA.2
  have h1 : Nat.card (PSU3Model 0) ≤ Nat.card (Subgroup.closure U) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have h2 := Subgroup.card_le_of_le hle
  have h3 : Nat.card (middleFixed (GaloisField 2 (2 * 0))) ≤ 16 := by
    have h16 : Nat.card (GaloisField 2 (2 * 0) × GaloisField 2 (2 * 0) ×
        GaloisField 2 (2 * 0) × GaloisField 2 (2 * 0)) = 16 := by
      simp only [Nat.card_prod, hF]
    rw [← h16]
    exact Nat.card_le_card_of_injective _ middleFixed_injective
  omega


theorem card_bounds_of_isSimpleBenderGroup
    {L : Type} [Group L] [Finite L]
    (hL : IsSimpleBenderGroup L) : 60 ≤ Nat.card L ∧ Nat.card L ≠ 72 := by
  rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨f, hf, E, _, _, J, hform, hEcard, hfixed, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, lemma114_psl2Binary_card_formula f (by omega)]
    rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · norm_num
    · have h8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
      have h63 : 63 ≤ (2 ^ f) ^ 2 - 1 := by
        have : 64 ≤ (2 ^ f) ^ 2 := by nlinarith
        omega
      have := Nat.mul_le_mul h8 h63
      constructor <;> omega
  · rw [Nat.card_congr e.toEquiv, lemma114_suzukiMatrixGroup_card_formula m (by omega)]
    have h8 : 8 ≤ 2 ^ (2 * m + 1) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 2 * m + 1))
    have h64 : 64 ≤ (2 ^ (2 * m + 1)) ^ 2 := by nlinarith
    have h7 : 7 ≤ 2 ^ (2 * m + 1) - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right h64 1) h64) h7
    constructor <;> omega
  · rw [Nat.card_congr e.toEquiv,
      CFSG.ShultStronglyClosedTI.unitaryCover_native_card J (2 ^ f) hEcard hfixed hform]
    have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
    have h64 : 64 ≤ (2 ^ f) ^ 3 := by nlinarith
    have h15 : 15 ≤ (2 ^ f) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
      omega
    have hN := Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right h64 1) h64) h15
    have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 := Nat.div_le_div_left hg hg0
      (a := ((2 ^ f) ^ 3 + 1) * (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1))
    have h2 := Nat.div_le_div_right (c := 3) hN
    constructor <;> omega

theorem false_of_mulEquiv_psu3Model_of_lt_two
    {L : Type} [Group L] [Finite L]
    (hL : IsSimpleBenderGroup L) {n : ℕ} (hn : n < 2) (e : L ≃* PSU3Model n) : False := by
  obtain ⟨h60, h72⟩ := card_bounds_of_isSimpleBenderGroup hL
  rw [Nat.card_congr e.toEquiv] at h60 h72
  interval_cases n
  · have := card_psu3Model_zero_le
    omega
  · exact h72 card_psu3Model_one

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
