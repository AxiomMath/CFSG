module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner
public import CFSG.RankThree.PartOne.LIT.CongruenceFive
public import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open Matrix Module CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₃" => Matrix (Fin 3) (Fin 3) F

@[expose] def rotJ : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def rot3 (F : Type) [Field F] : SL(3, F) := blockSL F 3 2 0 (by norm_num) rotJ

theorem coe_rot3 : (rot3 F : 𝕄₃) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [rot3, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotJ]

theorem coe_rot3_sq : ((rot3 F ^ 2 : SL(3, F)) : 𝕄₃) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, coe_rot3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rot3_pow_four : rot3 F ^ 4 = 1 := by
  have h : rot3 F ^ 4 = (rot3 F ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_rot3_sq, pow_two, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rot3_sq_ne_one (h2 : (2 : F) ≠ 0) : rot3 F ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(3, F) => (g : 𝕄₃) 0 0) h
  simp only [coe_rot3_sq, Matrix.SpecialLinearGroup.coe_one] at this
  apply h2
  simp at this
  linear_combination -this

theorem diagonal_mul_rot3 {d : Fin 3 → F} (hd : d 0 = d 1) :
    Matrix.diagonal d * (rot3 F : 𝕄₃) = (rot3 F : 𝕄₃) * Matrix.diagonal d := by
  rw [coe_rot3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd]

theorem rot3_transpose_mul_diagonal (a c : F) :
    (rot3 F : 𝕄₃)ᵀ * Matrix.diagonal ![a, a, c] * (rot3 F : 𝕄₃) = Matrix.diagonal ![a, a, c] := by
  rw [coe_rot3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem exists_sq_eq_of_mul_self {M : 𝕄₃} {c : F} (hdet : M.det ≠ 0) (hM : M * M = c • 1) :
    ∃ μ : F, μ ≠ 0 ∧ μ * μ = c := by
  have hc3 : M.det * M.det = c ^ 3 := by
    have := congrArg Matrix.det hM
    rw [det_mul, det_smul, det_one] at this
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hdet hdet (by simpa using hc3)
  refine ⟨M.det / c, div_ne_zero hdet hc0, ?_⟩
  field_simp
  linear_combination hc3

theorem inv_smul_mul_self {M : 𝕄₃} {c μ : F} (hμ0 : μ ≠ 0) (hμμ : μ * μ = c)
    (hM : M * M = c • 1) : (μ⁻¹ • M) * (μ⁻¹ • M) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul, smul_smul]
  have : μ⁻¹ * μ⁻¹ * c = 1 := by
    rw [← hμμ]
    field_simp
  rw [this, one_smul]

theorem conj_comm_matrix {n : Type*} [Fintype n] [DecidableEq n] {B P Q g M : Matrix n n F}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hBP : B * P = P * M) (hMg : M * g = g * M) :
    B * (P * g * Q) = P * g * Q * B := by
  have hBQ : Q * B = M * Q := by
    calc Q * B = Q * B * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (B * P) * Q := by simp only [Matrix.mul_assoc]
      _ = M * Q := by rw [hBP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  calc B * (P * g * Q) = (B * P) * g * Q := by simp only [Matrix.mul_assoc]
    _ = P * (M * g) * Q := by rw [hBP]; simp only [Matrix.mul_assoc]
    _ = P * (g * M) * Q := by rw [hMg]
    _ = P * g * (M * Q) := by simp only [Matrix.mul_assoc]
    _ = P * g * Q * B := by rw [← hBQ]; simp only [Matrix.mul_assoc]

theorem conj_fixed_matrix {n : Type*} [Fintype n] [DecidableEq n]
    {B Bi P Q g M : Matrix n n F} (hBBi : B * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hBP : B * P = P * M) (hMg : M * g = g * M) : B * (P * g * Q) * Bi = P * g * Q := by
  rw [conj_comm_matrix hPQ hQP hBP hMg, Matrix.mul_assoc _ B, hBBi, Matrix.mul_one]

theorem slConj_fixed_of_comm (B P : GL (Fin 3) F) (g : SL(3, F)) (M : 𝕄₃)
    (hBP : (B : 𝕄₃) * P = (P : 𝕄₃) * M) (hMg : M * (g : 𝕄₃) = (g : 𝕄₃) * M) :
    slConjugation 3 F B (slConjugation 3 F P g) = slConjugation 3 F P g := by
  apply Subtype.ext
  rw [slConjugation_matrix, slConjugation_matrix]
  exact conj_fixed_matrix (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hBP hMg

theorem exists_sl_conj_block (P : GL (Fin 3) F) :
    ∃ k : SL(3, F), ∀ X : SL(2, F), k * blockSL F 3 2 0 (by norm_num) X * k⁻¹ =
      slConjugation 3 F P (blockSL F 3 2 0 (by norm_num) X) := by
  set d : F := (P : 𝕄₃).det with hd
  have hd0 : d ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det P).isUnit
    simpa [hd] using this
  let D : 𝕄₃ := !![1, 0, 0; 0, 1, 0; 0, 0, d⁻¹]
  have hK : ((P : 𝕄₃) * D).det = 1 := by
    rw [det_mul, ← hd]
    simp [D, det_fin_three, hd0]
  obtain ⟨k, hk⟩ : ∃ k : SL(3, F), (k : 𝕄₃) = (P : 𝕄₃) * D := ⟨⟨_, hK⟩, rfl⟩
  refine ⟨k, fun X => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slConjugation_matrix,
    hk]
  have hPP : ((P⁻¹ : GL (Fin 3) F) : 𝕄₃) * (P : 𝕄₃) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDB : D * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) =
      ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) * D := by
    rw [coe_blockSL_three_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_three]
  calc (P : 𝕄₃) * D * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃)
      = (P : 𝕄₃) * (((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) * D) := by
        rw [Matrix.mul_assoc, hDB]
    _ = (P : 𝕄₃) * ((blockSL F 3 2 0 (by norm_num) X : SL(3, F)) : 𝕄₃) *
          (((P⁻¹ : GL (Fin 3) F) : 𝕄₃) * (P : 𝕄₃)) * D := by
        rw [hPP, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_sq_mul_eq {u v : F} (hv : v ≠ 0) (h : IsSquare (u * v)) :
    ∃ s : F, s * s * v = u := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r / v, ?_⟩
  field_simp
  linear_combination hr.symm

theorem exists_congr_diag_aa [Finite F] (h2 : (2 : F) ≠ 0) {R : 𝕄₃} (hR : Rᵀ = R)
    (hRdet : R.det ≠ 0) :
    ∃ (P : GL (Fin 3) F) (a c : F), a ≠ 0 ∧ c ≠ 0 ∧
      (P : 𝕄₃)ᵀ * R * (P : 𝕄₃) = Matrix.diagonal ![a, a, c] := by
  obtain ⟨g, d, hg⟩ := CFSG.RankThree.PartOne.LIT.exists_diagonal_congr h2 R hR
  have hg0 : (g : 𝕄₃).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).isUnit
    simpa using this
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hg, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hg0 hRdet) hg0
  rw [det_diagonal] at hdet
  have hd : ∀ i, d i ≠ 0 := fun i h => hdet (Finset.prod_eq_zero (Finset.mem_univ i) h)
  have hdd : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  have hx := hd 0
  have hy := hd 1
  have hz := hd 2
  obtain ⟨M, a, c, hM, ha, hc, hMd⟩ : ∃ (M : 𝕄₃) (a c : F), M.det ≠ 0 ∧ a ≠ 0 ∧ c ≠ 0 ∧
      Mᵀ * Matrix.diagonal d * M = Matrix.diagonal ![a, a, c] := by
    by_cases hxy : IsSquare (d 0 * d 1)
    · obtain ⟨s, hs⟩ := exists_sq_mul_eq hy hxy
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hs
        exact hx hs.symm
      refine ⟨!![1, 0, 0; 0, s, 0; 0, 0, 1], d 0, d 2, ?_, hx, hz, ?_⟩
      · simp [det_fin_three, hs0]
      · rw [hdd]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
        linear_combination hs
    · by_cases hxz : IsSquare (d 0 * d 2)
      · obtain ⟨s, hs⟩ := exists_sq_mul_eq hz hxz
        have hs0 : s ≠ 0 := by
          rintro rfl
          simp at hs
          exact hx hs.symm
        refine ⟨!![1, 0, 0; 0, 0, 1; 0, s, 0], d 0, d 1, ?_, hx, hy, ?_⟩
        · simp [det_fin_three, hs0]
        · rw [hdd]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
          linear_combination hs
      · have hsq := isSquare_mul_of_not hxy hxz
        have hyz : IsSquare (d 1 * d 2) := by
          obtain ⟨r, hr⟩ := hsq
          refine ⟨r / d 0, ?_⟩
          field_simp
          linear_combination hr
        obtain ⟨s, hs⟩ := exists_sq_mul_eq hz hyz
        have hs0 : s ≠ 0 := by
          rintro rfl
          simp at hs
          exact hy hs.symm
        refine ⟨!![0, 0, 1; 1, 0, 0; 0, s, 0], d 1, d 0, ?_, hy, hx, ?_⟩
        · simp [det_fin_three, hs0]
        · rw [hdd]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
          linear_combination hs
  let Mgl : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM
  refine ⟨g * Mgl, a, c, ha, hc, ?_⟩
  have hP : ((g * Mgl : GL (Fin 3) F) : 𝕄₃) = (g : 𝕄₃) * M := rfl
  rw [hP, Matrix.transpose_mul, ← hMd, ← hg]
  simp only [Matrix.mul_assoc]

theorem exists_eigen_matrix (hK : ringChar F ≠ 2) {B : 𝕄₃} (hB : B * B = 1) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F), d 0 = d 1 ∧
      B * (P : 𝕄₃) = (P : 𝕄₃) * Matrix.diagonal d := by
  have key : ∀ B' : 𝕄₃, B' * B' = 1 → 2 ≤ finrank F (LinearMap.ker (toLin' B' - 1)) →
      ∃ (P : GL (Fin 3) F) (d : Fin 3 → F), d 0 = d 1 ∧
        B' * (P : 𝕄₃) = (P : 𝕄₃) * Matrix.diagonal d := by
    intro B' hB' h2k
    obtain ⟨b, hb⟩ := exists_eigenbasis hK hB'
    set k := finrank F (LinearMap.ker (toLin' B' - 1)) with hk
    let d : Fin 3 → F := fun i => if (i : ℕ) < k then 1 else -1
    let P : GL (Fin 3) F := ⟨(Pi.basisFun F (Fin 3)).toMatrix b,
      b.toMatrix (Pi.basisFun F (Fin 3)), Basis.toMatrix_mul_toMatrix_flip _ _,
      Basis.toMatrix_mul_toMatrix_flip _ _⟩
    refine ⟨P, d, ?_, ?_⟩
    · have h0 : 0 < k := by omega
      have h1 : 1 < k := by omega
      simp [d, h0, h1]
    · ext r i
      have hP : ∀ s, (P : 𝕄₃) s i = b i s := fun s => by
        change ((Pi.basisFun F (Fin 3)).toMatrix b) s i = _
        simp [Basis.toMatrix_apply]
      have h3 := congrFun (hb i) r
      rw [Matrix.mul_diagonal, Matrix.mul_apply]
      simp only [hP]
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3
      rw [h3]
      simp only [d]
      ring
  by_cases h2k : 2 ≤ finrank F (LinearMap.ker (toLin' B - 1))
  · exact key B hB h2k
  · have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK hB)
    rw [finrank_fin_fun] at hsum
    have hker : LinearMap.ker (toLin' (-B) - 1) = LinearMap.ker (toLin' B + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    obtain ⟨P, d, hd, hP⟩ := key (-B) (by rw [neg_mul_neg, hB]) (by rw [hker]; omega)
    refine ⟨P, fun i => -d i, by simp [hd], ?_⟩
    have hdd : Matrix.diagonal (fun i => -d i) = -Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hdd, Matrix.mul_neg, ← hP, Matrix.neg_mul, neg_neg]

end CFSG.ClassicalInvolution.ModelFacts.MF15
