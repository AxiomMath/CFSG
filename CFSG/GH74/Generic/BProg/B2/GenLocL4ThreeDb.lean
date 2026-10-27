module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutDb
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2

local notation "K3" => ZMod 3

theorem orth2_pow8 : ∀ (b₁ b₂ : K3) (M : Matrix (Fin 2) (Fin 2) K3), b₁ ≠ 0 → b₂ ≠ 0 →
    M * !![b₁, 0; 0, b₂] * Mᵀ = !![b₁, 0; 0, b₂] → M ^ 8 = 1 := by
  decide

namespace GenLocL4ThreeDb

open GenLocL4Out

@[expose] def Gu : Matrix (Fin 4) (Fin 4) K3 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

@[expose] def W12 : Matrix (Fin 4) (Fin 4) K3 := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

@[expose] def W13 : Matrix (Fin 4) (Fin 4) K3 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]

theorem Gt_mul_Gs : (Gt : Matrix (Fin 4) (Fin 4) K3) * Gs = Gu := by decide
theorem Gs_mul_Gu : (Gs : Matrix (Fin 4) (Fin 4) K3) * Gu = Gt := by decide
theorem Gt_mul_Gu : (Gt : Matrix (Fin 4) (Fin 4) K3) * Gu = Gs := by decide
theorem W12_sq : W12 * W12 = 1 := by decide
theorem W13_sq : W13 * W13 = 1 := by decide
theorem W12_symm : W12ᵀ = W12 := by decide
theorem W13_symm : W13ᵀ = W13 := by decide
theorem W12_Gs : W12 * (Gs : Matrix (Fin 4) (Fin 4) K3) * W12 = Gt := by decide
theorem W13_Gu : W13 * Gu * W13 = (Gt : Matrix (Fin 4) (Fin 4) K3) := by decide

theorem bd2_pow (A B : Matrix (Fin 2) (Fin 2) K3) (n : ℕ) : bd2 A B ^ n = bd2 (A ^ n) (B ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, bd2_one]
  | succ n ih => rw [pow_succ, ih, bd2_mul, ← pow_succ, ← pow_succ]

theorem bd2_transpose (A B : Matrix (Fin 2) (Fin 2) K3) : (bd2 A B)ᵀ = bd2 Aᵀ Bᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bd2]

theorem diagonal_eq_bd2 (m : Fin 4 → K3) :
    (Matrix.diagonal m : Matrix (Fin 4) (Fin 4) K3) = bd2 !![m 0, 0; 0, m 1] !![m 2, 0; 0, m 3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bd2]


theorem pow8_block01 (z : Matrix (Fin 4) (Fin 4) K3) (m : Fin 4 → K3) (hm : ∀ i, m i ≠ 0)
    (hz : z * Gt = Gt * z) (h : z * Matrix.diagonal m * zᵀ = Matrix.diagonal m) : z ^ 8 = 1 := by
  obtain ⟨b02, b03, b12, b13, b20, b30, b21, b31⟩ := blocks_vanish Gt z (by decide) rfl hz.symm
  have hz' := eq_bd2 z b02 b03 b12 b13 b20 b30 b21 b31
  obtain ⟨Y1, Y2, hzY⟩ : ∃ Y1 Y2 : Matrix (Fin 2) (Fin 2) K3, z = bd2 Y1 Y2 := ⟨_, _, hz'⟩
  subst hzY
  rw [diagonal_eq_bd2, bd2_transpose, bd2_mul, bd2_mul] at h
  obtain ⟨e1, e2⟩ := bd2_inj h
  rw [bd2_pow, orth2_pow8 (m 0) (m 1) Y1 (hm 0) (hm 1) e1, orth2_pow8 (m 2) (m 3) Y2 (hm 2) (hm 3) e2, bd2_one]

theorem cj_mul {W : Matrix (Fin 4) (Fin 4) K3} (hW : W * W = 1) (a b : Matrix (Fin 4) (Fin 4) K3) :
    W * (a * b) * W = (W * a * W) * (W * b * W) := by
  have : (W * a * W) * (W * b * W) = W * a * (W * W) * b * W := by simp only [Matrix.mul_assoc]
  rw [this, hW, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem cj_cj {W : Matrix (Fin 4) (Fin 4) K3} (hW : W * W = 1) (a : Matrix (Fin 4) (Fin 4) K3) :
    W * (W * a * W) * W = a := by
  have : W * (W * a * W) * W = (W * W) * a * (W * W) := by simp only [Matrix.mul_assoc]
  rw [this, hW, Matrix.one_mul, Matrix.mul_one]

theorem cj_pow {W : Matrix (Fin 4) (Fin 4) K3} (hW : W * W = 1) (a : Matrix (Fin 4) (Fin 4) K3) (n : ℕ) :
    (W * a * W) ^ n = W * a ^ n * W := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hW]
  | succ n ih => rw [pow_succ, ih, pow_succ, cj_mul hW]

theorem cj_transpose {W : Matrix (Fin 4) (Fin 4) K3} (hWt : Wᵀ = W) (a : Matrix (Fin 4) (Fin 4) K3) :
    (W * a * W)ᵀ = W * aᵀ * W := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hWt, Matrix.mul_assoc]

theorem pow8_block_of_conj (W : Matrix (Fin 4) (Fin 4) K3) (hW : W * W = 1) (hWt : Wᵀ = W)
    (G : Matrix (Fin 4) (Fin 4) K3) (m m' : Fin 4 → K3) (hG : W * G * W = Gt)
    (hm : W * Matrix.diagonal m * W = Matrix.diagonal m') (hm0 : ∀ i, m' i ≠ 0)
    (z : Matrix (Fin 4) (Fin 4) K3) (hz : z * G = G * z)
    (h : z * Matrix.diagonal m * zᵀ = Matrix.diagonal m) : z ^ 8 = 1 := by
  have h1 : (W * z * W) * Gt = Gt * (W * z * W) := by
    rw [← hG, ← cj_mul hW, ← cj_mul hW, hz]
  have h2 : (W * z * W) * Matrix.diagonal m' * (W * z * W)ᵀ = Matrix.diagonal m' := by
    rw [← hm, cj_transpose hWt, ← cj_mul hW, ← cj_mul hW, h]
  have h3 := pow8_block01 (W * z * W) m' hm0 h1 h2
  rw [cj_pow hW] at h3
  calc z ^ 8 = W * (W * z ^ 8 * W) * W := (cj_cj hW _).symm
    _ = 1 := by rw [h3, Matrix.mul_one, hW]

theorem pow8_block02 (z : Matrix (Fin 4) (Fin 4) K3) (m : Fin 4 → K3) (hm : ∀ i, m i ≠ 0)
    (hz : z * Gs = Gs * z) (h : z * Matrix.diagonal m * zᵀ = Matrix.diagonal m) : z ^ 8 = 1 := by
  refine pow8_block_of_conj W12 W12_sq W12_symm Gs m ![m 0, m 2, m 1, m 3] W12_Gs ?_ ?_ z hz h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [W12, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_diagonal]
  · intro i
    fin_cases i <;> simp [hm]

theorem pow8_block03 (z : Matrix (Fin 4) (Fin 4) K3) (m : Fin 4 → K3) (hm : ∀ i, m i ≠ 0)
    (hz : z * Gu = Gu * z) (h : z * Matrix.diagonal m * zᵀ = Matrix.diagonal m) : z ^ 8 = 1 := by
  refine pow8_block_of_conj W13 W13_sq W13_symm Gu m ![m 0, m 3, m 2, m 1] W13_Gu ?_ ?_ z hz h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [W13, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_diagonal]
  · intro i
    fin_cases i <;> simp [hm]

theorem pow8_diag (z : Matrix (Fin 4) (Fin 4) K3) (hdet : z.det = 1) (h1 : z * Gt = Gt * z) (h2 : z * Gs = Gs * z) :
    z ^ 8 = 1 := by
  have hd := diag_of_comm (by decide : (2 : K3) ≠ 0) z h1.symm h2.symm
  have hne : ∀ i, z i i ≠ 0 := by
    intro i hi
    have h0 := hdet
    rw [hd, Matrix.det_diagonal] at h0
    have := Finset.prod_eq_zero (f := fun j => z j j) (Finset.mem_univ i) hi
    rw [this] at h0
    exact zero_ne_one h0
  have hsq : z * z = 1 := by
    conv_lhs => rw [hd]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    have key : ∀ a : K3, a ≠ 0 → a * a = 1 := by decide
    exact key _ (hne i)
  calc z ^ 8 = (z * z) ^ 4 := by rw [← pow_two, ← pow_mul]
    _ = 1 := by rw [hsq, one_pow]


theorem entry_zero_of_comm_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) K3) (v : Fin n → K3)
    (h : A * Matrix.diagonal v = Matrix.diagonal v * A) (i j : Fin n) (hij : v i ≠ v j) : A i j = 0 := by
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have h2 : A i j * (v j - v i) = 0 := by linear_combination this
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hij.symm)

theorem eq_diagonal_of_comm_two (A : Matrix (Fin 4) (Fin 4) K3)
    (h1 : A * Matrix.diagonal ![(-1 : K3), -1, 1, 1] = Matrix.diagonal ![(-1 : K3), -1, 1, 1] * A)
    (h2 : A * Matrix.diagonal ![(-1 : K3), 1, -1, 1] = Matrix.diagonal ![(-1 : K3), 1, -1, 1] * A) :
    A = Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact entry_zero_of_comm_diag A _ h1 _ _ (by decide)
      | exact entry_zero_of_comm_diag A _ h2 _ _ (by decide)

theorem comm_of_conj_eq {Am Ai d : Matrix (Fin 4) (Fin 4) K3} (hAiA : Ai * Am = 1) (h : Am * d * Ai = d) :
    Am * d = d * Am := by
  calc Am * d = Am * d * (Ai * Am) := by rw [hAiA, Matrix.mul_one]
    _ = (Am * d * Ai) * Am := by simp only [Matrix.mul_assoc]
    _ = d * Am := by rw [h]

@[expose] def dd1 : SL(4, K3) :=
  ⟨Matrix.diagonal ![(-1 : K3), -1, 1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

@[expose] def dd2 : SL(4, K3) :=
  ⟨Matrix.diagonal ![(-1 : K3), 1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

theorem dd1_inv : dd1⁻¹ = dd1 := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_one, dd1]
  decide

theorem dd2_inv : dd2⁻¹ = dd2 := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_one, dd2]
  decide

end GenLocL4ThreeDb

open GenLocL4ThreeDb GenLocL4Out in
theorem sq_eq_one_of_fix_diag (φ : MulAut SL(4, K3))
    (h : ∀ g : SL(4, K3), (g : Matrix (Fin 4) (Fin 4) K3).IsDiag → φ g = g) : φ * φ = 1 := by
  obtain ⟨A, σ, hform⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (by norm_num : 3 ≤ 4) φ
  have hσ : ∀ a : K3, σ a = a := fun a => by
    have := RingHom.ext_zmod (σ : K3 →+* K3) (RingHom.id K3)
    exact congrArg (fun f => f a) this
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) K3, M.map σ = M := fun M => by
    ext i j; simp [hσ]
  set Am : Matrix (Fin 4) (Fin 4) K3 := (A : Matrix (Fin 4) (Fin 4) K3) with hAm
  set Ai : Matrix (Fin 4) (Fin 4) K3 := ((A⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) with hAi
  have hAAi : Am * Ai = 1 := coe_mul_inv A
  have hAiA : Ai * Am = 1 := coe_inv_mul A
  have hconj : (∀ g : SL(4, K3), ((φ g : SL(4, K3)) : Matrix (Fin 4) (Fin 4) K3) = Am * (g : Matrix (Fin 4) (Fin 4) K3) * Ai) ∨
      (∀ g : SL(4, K3), ((φ g : SL(4, K3)) : Matrix (Fin 4) (Fin 4) K3) =
        Am * ((g⁻¹ : SL(4, K3)) : Matrix (Fin 4) (Fin 4) K3)ᵀ * Ai) := by
    rcases hform with h' | h'
    · left; intro g; rw [h' g, hmap]
    · right; intro g; rw [h' g, hmap]
  have hφd : ∀ d : SL(4, K3), d⁻¹ = d → (d : Matrix (Fin 4) (Fin 4) K3)ᵀ = d →
      (d : Matrix (Fin 4) (Fin 4) K3).IsDiag → Am * (d : Matrix (Fin 4) (Fin 4) K3) * Ai = d := by
    intro d hinv htr hdiag
    have e : ((φ d : SL(4, K3)) : Matrix (Fin 4) (Fin 4) K3) = (d : Matrix (Fin 4) (Fin 4) K3) :=
      congrArg Subtype.val (h d hdiag)
    rcases hconj with hc | hc
    · rw [hc d] at e; exact e
    · rw [hc d, hinv, htr] at e; exact e
  have c1 : Am * (dd1 : Matrix (Fin 4) (Fin 4) K3) * Ai = dd1 :=
    hφd dd1 dd1_inv (by simp [dd1]) (by simp [dd1])
  have c2 : Am * (dd2 : Matrix (Fin 4) (Fin 4) K3) * Ai = dd2 :=
    hφd dd2 dd2_inv (by simp [dd2]) (by simp [dd2])
  have hdiag := eq_diagonal_of_comm_two Am (comm_of_conj_eq hAiA c1) (comm_of_conj_eq hAiA c2)
  have hne : ∀ i, Am i i ≠ 0 := by
    intro i hi
    have e := congrFun (congrFun hAAi i) i
    rw [hdiag] at e
    simp only [Matrix.diagonal_mul, Matrix.one_apply_eq] at e
    rw [hi, zero_mul] at e
    exact zero_ne_one e
  have hsq : Am * Am = 1 := by
    conv_lhs => rw [hdiag]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    have key : ∀ a : K3, a ≠ 0 → a * a = 1 := by decide
    exact key _ (hne i)
  have hAieq : Ai = Am := by
    calc Ai = (Am * Am) * Ai := by rw [hsq, Matrix.one_mul]
      _ = Am * (Am * Ai) := by rw [Matrix.mul_assoc]
      _ = Am := by rw [hAAi, Matrix.mul_one]
  have hAmt : Amᵀ = Am := by
    have : Amᵀ = (Matrix.diagonal fun i => Am i i)ᵀ := by rw [← hdiag]
    rw [this, Matrix.diagonal_transpose, ← hdiag]
  refine MulEquiv.ext fun g => ?_
  apply Subtype.ext
  show ((φ (φ g) : SL(4, K3)) : Matrix (Fin 4) (Fin 4) K3) = g
  rcases hconj with hc | hc
  · rw [hc (φ g), hc g, hAieq]
    calc Am * (Am * (g : Matrix (Fin 4) (Fin 4) K3) * Am) * Am = (Am * Am) * g * (Am * Am) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hsq, Matrix.one_mul, Matrix.mul_one]
  · rw [hc (φ g), ← map_inv, hc g⁻¹, inv_inv, hAieq]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hAmt]
    calc Am * (Am * ((g : Matrix (Fin 4) (Fin 4) K3) * Am)) * Am = (Am * Am) * g * (Am * Am) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hsq, Matrix.one_mul, Matrix.mul_one]

end CFSG.GH74.Generic.BProg.B2
