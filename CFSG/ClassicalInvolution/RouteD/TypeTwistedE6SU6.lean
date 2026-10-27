module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Frame
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
import CFSG.ClassicalInvolution.Phan.BlockSingle

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models (IsLongRootSU2)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive
  exists_unitaryInvolution_eq_neg)
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply frobQ_frobQ)
open scoped MatrixGroups

section Sel

variable {E : Type} [Field E]

theorem antidiag_six_mul_sel :
    (antidiag 6 : Matrix (Fin 6) (Fin 6) E) * blockSel E 6 4 1 =
      blockSel E 6 4 1 * antidiag 4 := by
  ext a j
  show (∑ b, antidiag 6 a b * blockSel E 6 4 1 b j) = ∑ k, blockSel E 6 4 1 a k * antidiag 4 k j
  simp only [Fin.sum_univ_six, Fin.sum_univ_four]
  fin_cases a <;> fin_cases j <;> simp [antidiag, blockSel_apply, Fin.rev, Fin.ext_iff]

theorem sel_transpose_mul_antidiag_six :
    (blockSel E 6 4 1)ᵀ * (antidiag 6 : Matrix (Fin 6) (Fin 6) E) =
      antidiag 4 * (blockSel E 6 4 1)ᵀ := by
  ext j a
  show (∑ b, (blockSel E 6 4 1)ᵀ j b * antidiag 6 b a) =
    ∑ k, antidiag 4 j k * (blockSel E 6 4 1)ᵀ k a
  simp only [Fin.sum_univ_six, Fin.sum_univ_four]
  fin_cases a <;> fin_cases j <;>
    simp [antidiag, blockSel_apply, Fin.rev, Fin.ext_iff, Matrix.transpose_apply]

theorem form_blockMat_six (ψ : E ≃+* E) (X : Matrix (Fin 4) (Fin 4) E)
    (hX : conjTr ψ X * antidiag 4 * X = antidiag 4) :
    conjTr ψ (blockMat 6 1 X) * antidiag 6 * blockMat 6 1 X = antidiag 6 := by
  set L : Matrix (Fin 6) (Fin 4) E := blockSel E 6 4 1 with hL
  set Lt : Matrix (Fin 4) (Fin 6) E := L.transpose with hLt
  set A6 : Matrix (Fin 6) (Fin 6) E := antidiag 6 with hA6
  set A4 : Matrix (Fin 4) (Fin 4) E := antidiag 4 with hA4
  have e1 : A6 * L = L * A4 := antidiag_six_mul_sel
  have e2 : Lt * A6 = A4 * Lt := sel_transpose_mul_antidiag_six
  have e3 : Lt * L = 1 := blockSel_transpose_mul_self (by norm_num)
  set P : Matrix (Fin 4) (Fin 4) E := conjTr ψ X - 1 with hP
  set Q : Matrix (Fin 4) (Fin 4) E := X - 1 with hQ
  have hX' : (1 + P) * A4 * (1 + Q) = A4 := by
    rw [hP, hQ]
    simpa using hX
  have hcond : P * A4 + A4 * Q + P * A4 * Q = 0 := by
    have e : (1 + P) * A4 * (1 + Q) = A4 + (P * A4 + A4 * Q + P * A4 * Q) := by noncomm_ring
    rw [e] at hX'
    exact add_eq_left.mp hX'
  have hconj : conjTr ψ (blockMat 6 1 X) = 1 + L * P * Lt := by
    rw [conjTr_blockMat]
    unfold blockMat
    rw [hP, hL]
  have hblock : blockMat 6 1 X = 1 + L * Q * Lt := by
    unfold blockMat
    rw [hQ, hL]
  rw [hconj, hblock]
  have e1' : ∀ {n : ℕ} (M : Matrix (Fin 4) (Fin n) E), A6 * (L * M) = L * (A4 * M) := by
    intro n M
    rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc]
  have e3' : ∀ {n : ℕ} (N : Matrix (Fin 4) (Fin n) E), Lt * (L * N) = N := by
    intro n N
    rw [← Matrix.mul_assoc, e3, Matrix.one_mul]
  have step : (1 + L * P * Lt) * A6 * (1 + L * Q * Lt) =
      A6 + L * ((P * A4 + A4 * Q + P * A4 * Q) * Lt) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    have e6 : Lt * A6 = A4 * Lt := e2
    simp only [e1', e3', e6]
    abel
  rw [step, hcond]
  simp

end Sel

section Skew

variable {E : Type} [Field E]

theorem unitaryJInv_mul_unitaryJ : (unitaryJInv : Matrix (Fin 4) (Fin 4) E) * unitaryJ = 1 :=
  mul_eq_one_comm.mp unitaryJ_mul

theorem conjTr_mul_unitaryJInv_mul_of_sigmaA (ψ : E ≃+* E) {g : SL(4, E)}
    (hg : sigmaA ψ g = g) :
    conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E) =
      unitaryJInv := by
  set Mi : SL(4, E) := (fieldAutSL ψ 4 g)⁻¹ with hMi
  have h1 : ((sigmaA ψ g : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      unitaryJ * (Mi : Matrix (Fin 4) (Fin 4) E)ᵀ * unitaryJInv := rfl
  rw [hg] at h1
  have h2 : (Mi : Matrix (Fin 4) (Fin 4) E) *
      ((fieldAutSL ψ 4 g : SL(4, E)) : Matrix _ _ E) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hMi, inv_mul_cancel]
    rfl
  have h3 : conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * (Mi : Matrix (Fin 4) (Fin 4) E)ᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    exact this
  calc conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * unitaryJInv * (g : Matrix (Fin 4) (Fin 4) E)
      = conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * unitaryJInv *
        (unitaryJ * (Mi : Matrix (Fin 4) (Fin 4) E)ᵀ * unitaryJInv) := by rw [← h1]
    _ = conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * (unitaryJInv * unitaryJ) *
        (Mi : Matrix (Fin 4) (Fin 4) E)ᵀ * unitaryJInv := by simp only [Matrix.mul_assoc]
    _ = unitaryJInv := by rw [unitaryJInv_mul_unitaryJ, Matrix.mul_one, h3, Matrix.one_mul]

@[expose] def Dm (μ : E) : Matrix (Fin 4) (Fin 4) E := Matrix.diagonal ![1, 1, -μ, μ]

@[expose] def Dinv (μ : E) : Matrix (Fin 4) (Fin 4) E := Matrix.diagonal ![1, 1, -μ⁻¹, μ⁻¹]

theorem Dm_mul_Dinv {μ : E} (hμ : μ ≠ 0) : Dm μ * Dinv μ = 1 := by
  unfold Dm Dinv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hμ]

theorem conjTr_diagonal {n : ℕ} (ψ : E ≃+* E) (d : Fin n → E) :
    conjTr ψ (Matrix.diagonal d) = Matrix.diagonal (fun i => ψ (d i)) := by
  ext i j
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem conjTr_Dm_mul {μ : E} (ψ : E ≃+* E) (hμ : ψ μ = -μ) :
    conjTr ψ (Dm μ) * antidiag 4 * Dm μ = μ • (unitaryJInv : Matrix (Fin 4) (Fin 4) E) := by
  unfold Dm
  rw [conjTr_diagonal]
  ext i j
  show (∑ b, (∑ a, Matrix.diagonal (fun i => ψ (![1, 1, -μ, μ] i)) i a * antidiag 4 a b) *
    Matrix.diagonal ![1, 1, -μ, μ] b j) = μ * (unitaryJInv : Matrix (Fin 4) (Fin 4) E) i j
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, unitaryJInv, Fin.rev, Fin.ext_iff, hμ]

theorem form_Dm_of_sigmaA {μ : E} (hμ0 : μ ≠ 0) (ψ : E ≃+* E) (hμ : ψ μ = -μ) {g : SL(4, E)}
    (hg : sigmaA ψ g = g) :
    conjTr ψ (Dm μ * (g : Matrix (Fin 4) (Fin 4) E) * Dinv μ) * antidiag 4 *
      (Dm μ * (g : Matrix (Fin 4) (Fin 4) E) * Dinv μ) = antidiag 4 := by
  have hstar := conjTr_mul_unitaryJInv_mul_of_sigmaA ψ hg
  have hDD := Dm_mul_Dinv hμ0
  have hform := conjTr_Dm_mul ψ hμ
  have hconj1 : conjTr ψ (Dinv μ) * conjTr ψ (Dm μ) = 1 := by
    rw [← conjTr_mul, hDD, conjTr_one]
  rw [conjTr_mul, conjTr_mul]
  calc conjTr ψ (Dinv μ) * (conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * conjTr ψ (Dm μ)) *
        antidiag 4 * (Dm μ * (g : Matrix (Fin 4) (Fin 4) E) * Dinv μ)
      = conjTr ψ (Dinv μ) * conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) *
        (conjTr ψ (Dm μ) * antidiag 4 * Dm μ) * (g : Matrix (Fin 4) (Fin 4) E) * Dinv μ := by
        simp only [Matrix.mul_assoc]
    _ = μ • (conjTr ψ (Dinv μ) * (conjTr ψ (g : Matrix (Fin 4) (Fin 4) E) * unitaryJInv *
        (g : Matrix (Fin 4) (Fin 4) E)) * Dinv μ) := by
        rw [hform]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = conjTr ψ (Dinv μ) * (conjTr ψ (Dm μ) * antidiag 4 * Dm μ) * Dinv μ := by
        rw [hstar, hform]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = antidiag 4 := by
        calc conjTr ψ (Dinv μ) * (conjTr ψ (Dm μ) * antidiag 4 * Dm μ) * Dinv μ
            = (conjTr ψ (Dinv μ) * conjTr ψ (Dm μ)) * antidiag 4 * (Dm μ * Dinv μ) := by
              simp only [Matrix.mul_assoc]
          _ = antidiag 4 := by rw [hconj1, hDD, Matrix.one_mul, Matrix.mul_one]

end Skew

section Iota4

variable {E : Type} [Field E]

@[expose] def iota4SL (μ : E) (hμ0 : μ ≠ 0) : SL(4, E) →* SL(6, E) :=
  (blockSL E 6 4 1 (by norm_num)).comp (conjSL (Dm μ) (Dinv μ) (Dm_mul_Dinv hμ0)).toMonoidHom

theorem coe_iota4SL {μ : E} (hμ0 : μ ≠ 0) (g : SL(4, E)) :
    ((iota4SL μ hμ0 g : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      blockMat 6 1 (Dm μ * (g : Matrix (Fin 4) (Fin 4) E) * Dinv μ) :=
  rfl

theorem toGL_iota4SL_mem {σ : E ≃+* E} {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) {g : SL(4, E)}
    (hg : sigmaA σ g = g) :
    Matrix.SpecialLinearGroup.toGL (iota4SL μ hμ0 g) ∈ SU σ 6 := by
  rw [mem_SU]
  refine ⟨?_, ?_⟩
  · exact (iota4SL μ hμ0 g).2
  · exact form_blockMat_six σ _ (form_Dm_of_sigmaA hμ0 σ hμ hg)

end Iota4


section Iota3
variable {E : Type} [Field E]

@[expose] def tau3 (ψ : E ≃+* E) : SL(3, E) ≃* SL(3, E) :=
  (fieldAutSL ψ 3).trans ((invTransposeSL 3).trans
    (conjSL (antidiag 3) (antidiag 3) (antidiag_mul_self 3)))

theorem transvection_mul_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : E) :
    Matrix.SpecialLinearGroup.transvection hij a * Matrix.SpecialLinearGroup.transvection hij b =
      Matrix.SpecialLinearGroup.transvection hij (a + b) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [CFSG.LinearGroups.coe_transvection]
  have hz : (single i j a : Matrix (Fin n) (Fin n) E) * single i j b = 0 :=
    Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) b
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hz, add_zero,
    Matrix.single_add]
  abel

theorem coe_tau3_transvection (ψ : E ≃+* E) {i j : Fin 3} (hij : i ≠ j) (c : E) :
    ((tau3 ψ (Matrix.SpecialLinearGroup.transvection hij c) : SL(3, E)) :
      Matrix (Fin 3) (Fin 3) E) = 1 + single (Fin.rev j) (Fin.rev i) (-ψ c) := by
  have h1 : fieldAutSL ψ 3 (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (ψ c) := by
    refine Subtype.ext ?_
    rw [coe_fieldAutSL]
    simp only [CFSG.LinearGroups.coe_transvection]
    rw [Matrix.map_add _ (map_add ψ), Matrix.map_one _ (map_zero ψ) (map_one ψ),
      Matrix.map_single i j c ψ]
  have h2 : (Matrix.SpecialLinearGroup.transvection hij (ψ c))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (-ψ c) :=
    inv_eq_of_mul_eq_one_right (by rw [transvection_mul_transvection, add_neg_cancel]; ext; simp)
  show (antidiag 3 : Matrix (Fin 3) (Fin 3) E) *
      (((fieldAutSL ψ 3 (Matrix.SpecialLinearGroup.transvection hij c))⁻¹ : SL(3, E)) :
        Matrix (Fin 3) (Fin 3) E)ᵀ * antidiag 3 = _
  rw [h1, h2]
  simp only [CFSG.LinearGroups.coe_transvection]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, antidiag_mul_single, single_mul_antidiag,
    antidiag_mul_self]

@[expose] def iota3SL (ψ : E ≃+* E) : SL(3, E) →* SL(6, E) :=
  ((blockSL E 6 3 0 (by norm_num)).noncommCoprod (blockSL E 6 3 3 (by norm_num))
    (fun a b => blockSL_comm (by norm_num) (by norm_num) (Or.inl (by norm_num)) a b)).comp
    ((MonoidHom.id _).prod (tau3 ψ).toMonoidHom)

theorem iota3SL_apply (ψ : E ≃+* E) (g : SL(3, E)) :
    iota3SL ψ g = blockSL E 6 3 0 (by norm_num) g * blockSL E 6 3 3 (by norm_num) (tau3 ψ g) :=
  rfl

@[expose] def emb3 (i : Fin 3) : Fin 6 := ⟨i.val, by have := i.isLt; omega⟩

theorem emb3_injective : Function.Injective (emb3) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h
  simpa [emb3] using this)

theorem emb3_ne_rev (i : Fin 3) : emb3 i ≠ Fin.rev (emb3 i) := by
  intro h
  have := congrArg Fin.val h
  have := i.isLt
  simp [emb3, Fin.val_rev] at *
  omega

theorem coe_iota3SL_transvection (ψ : E ≃+* E) {i j : Fin 3} (hij : i ≠ j) (c : E) :
    ((iota3SL ψ (Matrix.SpecialLinearGroup.transvection hij c) : SL(6, E)) :
      Matrix (Fin 6) (Fin 6) E) = rootMatrix ψ (emb3 i) (emb3 j) c := by
  rw [iota3SL_apply, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL,
    coe_tau3_transvection, CFSG.LinearGroups.coe_transvection,
    blockMat_one_add_single (by norm_num), blockMat_one_add_single (by norm_num)]
  have hi := i.isLt
  have hj := j.isLt
  have hz : (single (⟨0 + i.val, by omega⟩ : Fin 6) (⟨0 + j.val, by omega⟩ : Fin 6) c :
      Matrix (Fin 6) (Fin 6) E) * single (⟨3 + (Fin.rev j).val, by omega⟩ : Fin 6)
        (⟨3 + (Fin.rev i).val, by omega⟩ : Fin 6) (-ψ c) = 0 := by
    apply Matrix.single_mul_single_of_ne
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_rev] at this
    omega
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hz, add_zero]
  unfold rootMatrix
  have e1 : (⟨0 + i.val, by omega⟩ : Fin 6) = emb3 i := Fin.ext (by simp [emb3])
  have e2 : (⟨0 + j.val, by omega⟩ : Fin 6) = emb3 j := Fin.ext (by simp [emb3])
  have e3 : (⟨3 + (Fin.rev j).val, by omega⟩ : Fin 6) = Fin.rev (emb3 j) :=
    Fin.ext (by simp [emb3, Fin.val_rev]; omega)
  have e4 : (⟨3 + (Fin.rev i).val, by omega⟩ : Fin 6) = Fin.rev (emb3 i) :=
    Fin.ext (by simp [emb3, Fin.val_rev]; omega)
  rw [e1, e2, e3, e4, ← Matrix.single_neg, sub_eq_add_neg]

end Iota3

section Hom3
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)

theorem toGL_iota3SL_transvection {i j : Fin 3} (hij : i ≠ j) (c : E) :
    Matrix.SpecialLinearGroup.toGL (iota3SL σ (Matrix.SpecialLinearGroup.transvection hij c)) =
      ((rootHom σ hσ (fun h => hij (emb3_injective h)) (emb3_ne_rev i) (emb3_ne_rev j)
        (Multiplicative.ofAdd c) : SU σ 6) : GL (Fin 6) E) := by
  refine Units.ext ?_
  show ((iota3SL σ (Matrix.SpecialLinearGroup.transvection hij c) : SL(6, E)) :
    Matrix (Fin 6) (Fin 6) E) = _
  rw [coe_iota3SL_transvection]
  rfl

include hσ in
theorem toGL_iota3SL_mem (g : SL(3, E)) :
    Matrix.SpecialLinearGroup.toGL (iota3SL σ g) ∈ SU σ 6 := by
  have hall : Subgroup.comap ((Matrix.SpecialLinearGroup.toGL).comp (iota3SL σ)) (SU σ 6) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation,
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    show Matrix.SpecialLinearGroup.toGL (iota3SL σ (Matrix.SpecialLinearGroup.transvection hij c))
      ∈ SU σ 6
    rw [toGL_iota3SL_transvection hσ hij c]
    exact (rootHom σ hσ (fun h => hij (emb3_injective h)) (emb3_ne_rev i) (emb3_ne_rev j)
      (Multiplicative.ofAdd c)).2
  have h2 : g ∈ Subgroup.comap ((Matrix.SpecialLinearGroup.toGL).comp (iota3SL σ)) (SU σ 6) := by
    rw [hall]
    exact Subgroup.mem_top g
  exact h2

include hσ in
@[expose] noncomputable def iota3 : SL(3, E) →* SU σ 6 :=
  ((Matrix.SpecialLinearGroup.toGL).comp (iota3SL σ)).codRestrict (SU σ 6)
    (toGL_iota3SL_mem hσ)

end Hom3

section Gens
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)

include hσ in
theorem rootGroup_le_of_gens {n : ℕ} (γ : Fin (n / 2) → ℤ) (H : Subgroup (SU σ n))
    (h1 : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
      j ≠ Fin.rev i → weight n i - weight n j = toStd n γ →
        ∀ c, rootHom σ hσ hij hi hj c ∈ H)
    (h2 : ∀ (i : Fin n) (hi : i ≠ Fin.rev i), 2 • weight n i = toStd n γ →
      ∀ c, longRootHom σ hi c ∈ H)
    (h3 : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
      weight n i = toStd n γ → heisenbergSubgroup σ hσ hi hik hk ≤ H) :
    rootGroup σ hσ n γ ≤ H := by
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    exact h1 i j hij hi hj hji hw c
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rintro _ ⟨c, rfl⟩
    exact h2 i hi hw c
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact h3 i k hi hik hk hw

end Gens

section Classify

theorem cls_short0 : ∀ a b : Fin 6, weight 6 a - weight 6 b = toStd 6 (Pi.single (0 : Fin 3) 1) →
    (a = 0 ∧ b = 1) ∨ (a = 4 ∧ b = 5) := by decide +kernel

theorem cls_short1 : ∀ a b : Fin 6, weight 6 a - weight 6 b = toStd 6 (Pi.single (1 : Fin 3) 1) →
    (a = 1 ∧ b = 2) ∨ (a = 3 ∧ b = 4) := by decide +kernel

end Classify

section Nodes3
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)

theorem blockSL_three_transvection {s : ℕ} (h : s + 2 ≤ 3) {a b : Fin 2} (hab : a ≠ b) (c : E) :
    blockSL E 3 2 s h (Matrix.SpecialLinearGroup.transvection hab c) =
      Matrix.SpecialLinearGroup.transvection (i := (⟨s + a.val, by omega⟩ : Fin 3))
        (j := (⟨s + b.val, by omega⟩ : Fin 3))
        (fun e => hab (Fin.ext (by have := congrArg Fin.val e; simp at this; omega))) c := by
  refine Subtype.ext ?_
  rw [coe_blockSL, CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection,
    blockMat_one_add_single h]

include hσ in
theorem rootMatrix_rev {n : ℕ} (i j : Fin n) (c : E) :
    rootMatrix σ (Fin.rev j) (Fin.rev i) c = rootMatrix σ i j (-σ c) := by
  unfold rootMatrix
  rw [Fin.rev_rev, Fin.rev_rev, map_neg, hσ, ← Matrix.single_neg, ← Matrix.single_neg]
  simp only [neg_neg, sub_eq_add_neg]
  abel

end Nodes3

theorem cls_short0_neg : ∀ a b : Fin 6,
    weight 6 a - weight 6 b = toStd 6 (-Pi.single (0 : Fin 3) 1) →
      (a = 1 ∧ b = 0) ∨ (a = 5 ∧ b = 4) := by decide +kernel

theorem cls_short1_neg : ∀ a b : Fin 6,
    weight 6 a - weight 6 b = toStd 6 (-Pi.single (1 : Fin 3) 1) →
      (a = 2 ∧ b = 1) ∨ (a = 4 ∧ b = 3) := by decide +kernel

theorem nolong_short (k : Fin 3) (hk : k ≠ 2) (i : Fin 6) :
    2 • weight 6 i ≠ toStd 6 (Pi.single k 1) ∧ 2 • weight 6 i ≠ toStd 6 (-Pi.single k 1) := by
  revert k i
  decide +kernel

theorem rev_ne_self_six : ∀ k : Fin 6, Fin.rev k ≠ k := by decide +kernel

section B12
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)

noncomputable abbrev nodeSU (k : Fin 3) : Subgroup (SU σ 6) :=
  rootGroup σ hσ 6 (Pi.single k 1) ⊔ rootGroup σ hσ 6 (-Pi.single k 1)

include hσ in
theorem iota3_blockSL_transvection {s : ℕ} (h : s + 2 ≤ 3) {a b : Fin 2} (hab : a ≠ b) (c : E) :
    iota3 hσ (blockSL E 3 2 s h (Matrix.SpecialLinearGroup.transvection hab c)) =
      rootHom σ hσ (i := emb3 ⟨s + a.val, by omega⟩) (j := emb3 ⟨s + b.val, by omega⟩)
        (fun e => hab (Fin.ext (by
          have := congrArg Fin.val e
          simp [emb3] at this
          omega)))
        (emb3_ne_rev _) (emb3_ne_rev _) (Multiplicative.ofAdd c) := by
  rw [blockSL_three_transvection]
  exact Subtype.ext (toGL_iota3SL_transvection hσ _ c)

include hσ in
theorem iota3_B12_le : (B12 E).map (iota3 hσ) ≤ nodeSU hσ 0 := by
  rintro _ ⟨x, ⟨x', rfl⟩, rfl⟩
  have hall : Subgroup.comap ((iota3 hσ).comp (blockSL E 3 2 0 (by norm_num))) (nodeSU hσ 0) =
      ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation,
      Subgroup.closure_le]
    rintro _ ⟨a, b, hab, c, rfl⟩
    show iota3 hσ (blockSL E 3 2 0 _ (Matrix.SpecialLinearGroup.transvection hab c)) ∈
      nodeSU hσ 0
    rw [iota3_blockSL_transvection hσ]
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact Subgroup.mem_sup_left
        (rootHom_mem hσ _ _ _ (by decide +kernel) (by decide +kernel) _)
    · exact Subgroup.mem_sup_right
        (rootHom_mem hσ _ _ _ (by decide +kernel) (by decide +kernel) _)
    · exact absurd rfl hab
  have h2 : x' ∈ Subgroup.comap ((iota3 hσ).comp (blockSL E 3 2 0 (by norm_num)))
      (nodeSU hσ 0) := by
    rw [hall]; exact Subgroup.mem_top x'
  exact h2

include hσ in
theorem rootHom_rev {n : ℕ} {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hij' : Fin.rev j ≠ Fin.rev i) (hj' : Fin.rev j ≠ Fin.rev (Fin.rev j))
    (hi' : Fin.rev i ≠ Fin.rev (Fin.rev i)) (c : Multiplicative E) :
    rootHom σ hσ hij' hj' hi' c = rootHom σ hσ hij hi hj (Multiplicative.ofAdd (-σ c.toAdd)) :=
  Subtype.ext (Units.ext (by
    show rootMatrix σ (Fin.rev j) (Fin.rev i) c.toAdd = rootMatrix σ i j (-σ c.toAdd)
    exact rootMatrix_rev hσ i j c.toAdd))

include hσ in
theorem iota3_B12_ge : nodeSU hσ 0 ≤ (B12 E).map (iota3 hσ) := by
  have hmem : ∀ (a b : Fin 2) (hab : a ≠ b) (c : E),
      iota3 hσ (blockSL E 3 2 0 (by norm_num) (Matrix.SpecialLinearGroup.transvection hab c)) ∈
        (B12 E).map (iota3 hσ) := fun a b hab c => ⟨_, ⟨_, rfl⟩, rfl⟩
  have h01 := hmem 0 1 (by decide)
  have h10 := hmem 1 0 (by decide)
  refine sup_le ?_ ?_
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      rcases cls_short0 i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e := iota3_blockSL_transvection hσ (s := 0) (by norm_num) (a := 0) (b := 1)
          (by decide) c.toAdd
        have h := h01 c.toAdd
        rw [e] at h
        exact h
      · have e := iota3_blockSL_transvection hσ (s := 0) (by norm_num) (a := 0) (b := 1)
          (by decide) (-σ c.toAdd)
        have h := h01 (-σ c.toAdd)
        rw [e] at h
        rw [show rootHom σ hσ hij hi hj c = _ from rootHom_rev hσ (i := (0 : Fin 6)) (j := 1)
          (by decide) (by decide +kernel) (by decide +kernel) _ _ _ c]
        exact h
    · intro i hi hw
      exact absurd hw (nolong_short 0 (by decide) i).1
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      rcases cls_short0_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e := iota3_blockSL_transvection hσ (s := 0) (by norm_num) (a := 1) (b := 0)
          (by decide) c.toAdd
        have h := h10 c.toAdd
        rw [e] at h
        exact h
      · have e := iota3_blockSL_transvection hσ (s := 0) (by norm_num) (a := 1) (b := 0)
          (by decide) (-σ c.toAdd)
        have h := h10 (-σ c.toAdd)
        rw [e] at h
        rw [show rootHom σ hσ hij hi hj c = _ from rootHom_rev hσ (i := (1 : Fin 6)) (j := 0)
          (by decide) (by decide +kernel) (by decide +kernel) _ _ _ c]
        exact h
    · intro i hi hw
      exact absurd hw (nolong_short 0 (by decide) i).2
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)

include hσ in
theorem iota3_B23_le : (B23 E).map (iota3 hσ) ≤ nodeSU hσ 1 := by
  rintro _ ⟨x, ⟨x', rfl⟩, rfl⟩
  have hall : Subgroup.comap ((iota3 hσ).comp (blockSL E 3 2 1 (by norm_num))) (nodeSU hσ 1) =
      ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation,
      Subgroup.closure_le]
    rintro _ ⟨a, b, hab, c, rfl⟩
    show iota3 hσ (blockSL E 3 2 1 _ (Matrix.SpecialLinearGroup.transvection hab c)) ∈
      nodeSU hσ 1
    rw [iota3_blockSL_transvection hσ]
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact Subgroup.mem_sup_left
        (rootHom_mem hσ _ _ _ (by decide +kernel) (by decide +kernel) _)
    · exact Subgroup.mem_sup_right
        (rootHom_mem hσ _ _ _ (by decide +kernel) (by decide +kernel) _)
    · exact absurd rfl hab
  have h2 : x' ∈ Subgroup.comap ((iota3 hσ).comp (blockSL E 3 2 1 (by norm_num)))
      (nodeSU hσ 1) := by
    rw [hall]; exact Subgroup.mem_top x'
  exact h2


include hσ in
theorem iota3_B23_ge : nodeSU hσ 1 ≤ (B23 E).map (iota3 hσ) := by
  have hmem : ∀ (a b : Fin 2) (hab : a ≠ b) (c : E),
      iota3 hσ (blockSL E 3 2 1 (by norm_num) (Matrix.SpecialLinearGroup.transvection hab c)) ∈
        (B23 E).map (iota3 hσ) := fun a b hab c => ⟨_, ⟨_, rfl⟩, rfl⟩
  have h01 := hmem 0 1 (by decide)
  have h10 := hmem 1 0 (by decide)
  refine sup_le ?_ ?_
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      rcases cls_short1 i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e := iota3_blockSL_transvection hσ (s := 1) (by norm_num) (a := 0) (b := 1)
          (by decide) c.toAdd
        have h := h01 c.toAdd
        rw [e] at h
        exact h
      · have e := iota3_blockSL_transvection hσ (s := 1) (by norm_num) (a := 0) (b := 1)
          (by decide) (-σ c.toAdd)
        have h := h01 (-σ c.toAdd)
        rw [e] at h
        rw [show rootHom σ hσ hij hi hj c = _ from rootHom_rev hσ (i := (1 : Fin 6)) (j := 2)
          (by decide) (by decide +kernel) (by decide +kernel) _ _ _ c]
        exact h
    · intro i hi hw
      exact absurd hw (nolong_short 1 (by decide) i).1
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      rcases cls_short1_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e := iota3_blockSL_transvection hσ (s := 1) (by norm_num) (a := 1) (b := 0)
          (by decide) c.toAdd
        have h := h10 c.toAdd
        rw [e] at h
        exact h
      · have e := iota3_blockSL_transvection hσ (s := 1) (by norm_num) (a := 1) (b := 0)
          (by decide) (-σ c.toAdd)
        have h := h10 (-σ c.toAdd)
        rw [e] at h
        rw [show rootHom σ hσ hij hi hj c = _ from rootHom_rev hσ (i := (2 : Fin 6)) (j := 1)
          (by decide) (by decide +kernel) (by decide +kernel) _ _ _ c]
        exact h
    · intro i hi hw
      exact absurd hw (nolong_short 1 (by decide) i).2
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)


end B12

section Hom4
variable {E : Type} [Field E] {σ : E ≃+* E} {θ : E →+* E} (hθ : ∀ c, θ (θ c) = c)
variable {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

include hθ hμ0 hμ hσθ in
theorem toGL_iota4SL_mem_of_mem {g : SL(4, E)} (hg : g ∈ unitaryGroup θ hθ) :
    Matrix.SpecialLinearGroup.toGL (iota4SL μ hμ0 g) ∈ SU σ 6 := by
  have hσe : involEquiv θ hθ = σ := RingEquiv.ext fun c => (hσθ c).symm
  have h := (mem_unitaryGroup θ hθ).mp hg
  rw [hσe] at h
  exact toGL_iota4SL_mem hμ0 hμ h

include hθ hμ0 hμ hσθ in
@[expose] noncomputable def iota4 : unitaryGroup θ hθ →* SU σ 6 :=
  (((Matrix.SpecialLinearGroup.toGL).comp (iota4SL μ hμ0)).comp
    (unitaryGroup θ hθ).subtype).codRestrict (SU σ 6)
    fun g => toGL_iota4SL_mem_of_mem hθ hμ0 hμ hσθ g.2

end Hom4

section Diag
variable {E : Type} [Field E]

theorem diagonal_mul_one_add_single_mul_diagonal {n : ℕ} (d d' : Fin n → E) (a b : Fin n) (t : E) :
    Matrix.diagonal d * (1 + Matrix.single a b t) * Matrix.diagonal d' =
      Matrix.diagonal (fun i => d i * d' i) + Matrix.single a b (d a * t * d' b) := by
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.single_apply]
  by_cases hax : a = x <;> by_cases hby : b = y <;> by_cases hxy : x = y
  all_goals simp_all
  all_goals (subst_vars; ring)

theorem Dm_conj_single {μ : E} (hμ0 : μ ≠ 0) (a b : Fin 4) (t : E) :
    Dm μ * (1 + Matrix.single a b t) * Dinv μ =
      1 + Matrix.single a b (![1, 1, -μ, μ] a * t * ![1, 1, -μ⁻¹, μ⁻¹] b) := by
  unfold Dm Dinv
  rw [diagonal_mul_one_add_single_mul_diagonal]
  congr 1
  have := Dm_mul_Dinv hμ0
  unfold Dm Dinv at this
  rw [Matrix.diagonal_mul_diagonal] at this
  exact this

theorem coe_liftSL_transvection {θ : E →+* E} {i j : Fin 2} (hij : i ≠ j) (s : fixedField θ) :
    ((liftSL θ 2 (Matrix.SpecialLinearGroup.transvection hij s) : SL(2, E)) :
      Matrix (Fin 2) (Fin 2) E) = 1 + Matrix.single i j (s : E) := by
  ext x y
  simp [liftSL, CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]

end Diag

section Eval4
variable {E : Type} [Field E] {θ : E →+* E} {μ : E} (hμ0 : μ ≠ 0)

theorem coe_iota4SL_ulbSL_upper (s : fixedField θ) :
    ((iota4SL μ hμ0 (ulbSL θ (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) s)) : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      longRootMatrix (2 : Fin 6) (-μ⁻¹ * (s : E)) := by
  rw [coe_iota4SL]
  show blockMat 6 1 (Dm μ * (blockMat 4 1 ((liftSL θ 2 (Matrix.SpecialLinearGroup.transvection
    (i := (0 : Fin 2)) (j := 1) (by decide) s) : SL(2, E)) : Matrix (Fin 2) (Fin 2) E)) *
      Dinv μ) = _
  rw [coe_liftSL_transvection, blockMat_one_add_single (by norm_num), Dm_conj_single hμ0,
    blockMat_one_add_single (by norm_num)]
  unfold longRootMatrix
  congr 2
  simp [mul_comm]

theorem coe_iota4SL_ulbSL_lower (s : fixedField θ) :
    ((iota4SL μ hμ0 (ulbSL θ (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) s)) : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      longRootMatrix (3 : Fin 6) (-μ * (s : E)) := by
  rw [coe_iota4SL]
  show blockMat 6 1 (Dm μ * (blockMat 4 1 ((liftSL θ 2 (Matrix.SpecialLinearGroup.transvection
    (i := (1 : Fin 2)) (j := 0) (by decide) s) : SL(2, E)) : Matrix (Fin 2) (Fin 2) E)) *
      Dinv μ) = _
  rw [coe_liftSL_transvection, blockMat_one_add_single (by norm_num), Dm_conj_single hμ0,
    blockMat_one_add_single (by norm_num)]
  unfold longRootMatrix
  congr 2
  simp

end Eval4

section Long
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {θ : E →+* E}
  (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

theorem cls_long : ∀ i : Fin 6, 2 • weight 6 i = toStd 6 (Pi.single (2 : Fin 3) 1) → i = 2 := by
  decide +kernel

theorem cls_long_neg :
    ∀ i : Fin 6, 2 • weight 6 i = toStd 6 (-Pi.single (2 : Fin 3) 1) → i = 3 := by
  decide +kernel

theorem cls_long_rev : ∀ a b : Fin 6, weight 6 a - weight 6 b = toStd 6 (Pi.single (2 : Fin 3) 1) →
    b = Fin.rev a := by decide +kernel

theorem cls_long_rev_neg : ∀ a b : Fin 6,
    weight 6 a - weight 6 b = toStd 6 (-Pi.single (2 : Fin 3) 1) → b = Fin.rev a := by
  decide +kernel

include hμ hσθ in
theorem traceZero_upper (s : fixedField θ) : -μ⁻¹ * (s : E) ∈ traceZero σ := by
  have hs : σ (s : E) = s := by rw [hσθ]; exact s.2
  rw [mem_traceZero, map_mul, map_neg, map_inv₀, hμ, hs]
  ring

include hμ hσθ in
theorem traceZero_lower (s : fixedField θ) : -μ * (s : E) ∈ traceZero σ := by
  have hs : σ (s : E) = s := by rw [hσθ]; exact s.2
  rw [mem_traceZero, map_mul, map_neg, hμ, hs]
  ring


include hθ hμ0 hμ hσθ in
theorem iota4_ulb_upper (s : fixedField θ) :
    iota4 hθ hμ0 hμ hσθ (ulb θ hθ (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) s)) =
      longRootHom σ (i := (2 : Fin 6)) (by decide)
        (Multiplicative.ofAdd (⟨-μ⁻¹ * (s : E), traceZero_upper hμ hσθ s⟩ : traceZero σ)) :=
  Subtype.ext (Units.ext (coe_iota4SL_ulbSL_upper hμ0 s))

include hθ hμ0 hμ hσθ in
theorem iota4_ulb_lower (s : fixedField θ) :
    iota4 hθ hμ0 hμ hσθ (ulb θ hθ (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) s)) =
      longRootHom σ (i := (3 : Fin 6)) (by decide)
        (Multiplicative.ofAdd (⟨-μ * (s : E), traceZero_lower hμ hσθ s⟩ : traceZero σ)) :=
  Subtype.ext (Units.ext (coe_iota4SL_ulbSL_lower hμ0 s))

include hσ hθ hμ0 hμ hσθ in
theorem iota4_ulb_le :
    ((ulb θ hθ).range).map (iota4 hθ hμ0 hμ hσθ) ≤ nodeSU hσ 2 := by
  rintro _ ⟨x, ⟨x', rfl⟩, rfl⟩
  have hall : Subgroup.comap ((iota4 hθ hμ0 hμ hσθ).comp (ulb θ hθ)) (nodeSU hσ 2) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation,
      Subgroup.closure_le]
    rintro _ ⟨a, b, hab, s, rfl⟩
    show iota4 hθ hμ0 hμ hσθ (ulb θ hθ (Matrix.SpecialLinearGroup.transvection hab s)) ∈
      nodeSU hσ 2
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · rw [iota4_ulb_upper hθ hμ0 hμ hσθ]
      exact Subgroup.mem_sup_left (longRootHom_mem hσ _ (by decide +kernel) _)
    · rw [iota4_ulb_lower hθ hμ0 hμ hσθ]
      exact Subgroup.mem_sup_right (longRootHom_mem hσ _ (by decide +kernel) _)
    · exact absurd rfl hab
  have h2 : x' ∈ Subgroup.comap ((iota4 hθ hμ0 hμ hσθ).comp (ulb θ hθ)) (nodeSU hσ 2) := by
    rw [hall]; exact Subgroup.mem_top x'
  exact h2

end Long

section Long2
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {θ : E →+* E}
  (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

include hσ hθ hμ0 hμ hσθ in
theorem iota4_ulb_ge :
    nodeSU hσ 2 ≤ ((ulb θ hθ).range).map (iota4 hθ hμ0 hμ hσθ) := by
  refine sup_le ?_ ?_
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      exact absurd (cls_long_rev i j hw) hji
    · intro i hi hw c
      have h2 : i = 2 := cls_long i hw
      subst h2
      have hc : σ (c.toAdd : E) = -(c.toAdd : E) :=
        eq_neg_of_add_eq_zero_right c.toAdd.2
      let s : fixedField θ := ⟨-μ * (c.toAdd : E), by
        rw [mem_fixedField, ← hσθ, map_mul, map_neg, hμ, hc]; ring⟩
      have e := iota4_ulb_upper hθ hμ0 hμ hσθ s
      have hpar : (⟨-μ⁻¹ * (s : E), traceZero_upper hμ hσθ s⟩ : traceZero σ) = c.toAdd :=
        Subtype.ext (by simp only [s]; field_simp)
      refine ⟨_, ⟨_, rfl⟩, e.trans ?_⟩
      rw [hpar]
      rfl
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)
  · refine rootGroup_le_of_gens hσ _ _ ?_ ?_ ?_
    · intro i j hij hi hj hji hw c
      exact absurd (cls_long_rev_neg i j hw) hji
    · intro i hi hw c
      have h2 : i = 3 := cls_long_neg i hw
      subst h2
      have hc : σ (c.toAdd : E) = -(c.toAdd : E) :=
        eq_neg_of_add_eq_zero_right c.toAdd.2
      let s : fixedField θ := ⟨-μ⁻¹ * (c.toAdd : E), by
        rw [mem_fixedField, ← hσθ, map_mul, map_neg, map_inv₀, hμ, hc]; ring⟩
      have e := iota4_ulb_lower hθ hμ0 hμ hσθ s
      have hpar : (⟨-μ * (s : E), traceZero_lower hμ hσθ s⟩ : traceZero σ) = c.toAdd :=
        Subtype.ext (by simp only [s]; field_simp)
      refine ⟨_, ⟨_, rfl⟩, e.trans ?_⟩
      rw [hpar]
      rfl
    · intro i k _ _ hk
      exact absurd hk (rev_ne_self_six k)

end Long2

section Short4
variable {E : Type} [Field E] {θ : E →+* E} (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0)

include hμ0 in
theorem Dinv_mul_Dm : Dinv μ * Dm μ = 1 := mul_eq_one_comm.mp (Dm_mul_Dinv hμ0)

include hθ in
theorem coe_iota4SL_usbSL_upper (c : E) :
    ((iota4SL μ hμ0 (usbSL θ hθ (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) c)) : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      1 + single (1 : Fin 6) 2 c + single (3 : Fin 6) 4 (-θ c) := by
  rw [coe_iota4SL, coe_usbSL]
  ext a b
  simp only [blockMat_apply, Dm, Dinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases a <;> fin_cases b
  all_goals simp [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, hμ0]
  all_goals field_simp

include hθ in
theorem coe_iota4SL_usbSL_lower (c : E) :
    ((iota4SL μ hμ0 (usbSL θ hθ (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) c)) : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) =
      1 + single (2 : Fin 6) 1 c + single (4 : Fin 6) 3 (-θ c) := by
  rw [coe_iota4SL, coe_usbSL]
  ext a b
  simp only [blockMat_apply, Dm, Dinv, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases a <;> fin_cases b
  all_goals simp [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, hμ0]
  all_goals field_simp

end Short4

section Cons
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {θ : E →+* E}
  (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

include hσ hθ hμ0 hμ hσθ in
theorem iota4_comp_usb :
    (iota4 hθ hμ0 hμ hσθ).comp (usb θ hθ) =
      (iota3 hσ).comp (blockSL E 3 2 1 (by norm_num)) := by
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 E) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top x
  refine MonoidHom.eqOn_closure (f := (iota4 hθ hμ0 hμ hσθ).comp (usb θ hθ))
    (g := (iota3 hσ).comp (blockSL E 3 2 1 (by norm_num))) ?_ hx
  rintro _ ⟨a, b, hab, c, rfl⟩
  show iota4 hθ hμ0 hμ hσθ (usb θ hθ (Matrix.SpecialLinearGroup.transvection hab c)) =
    iota3 hσ (blockSL E 3 2 1 _ (Matrix.SpecialLinearGroup.transvection hab c))
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · refine Subtype.ext (Units.ext ?_)
    refine (coe_iota4SL_usbSL_upper hθ hμ0 c).trans ?_
    show _ = ((iota3SL σ (blockSL E 3 2 1 _ (Matrix.SpecialLinearGroup.transvection hab c)) :
      SL(6, E)) : Matrix (Fin 6) (Fin 6) E)
    rw [blockSL_three_transvection, coe_iota3SL_transvection]
    unfold rootMatrix
    show 1 + single (1 : Fin 6) 2 c + single (3 : Fin 6) 4 (-θ c) =
      1 + single (1 : Fin 6) 2 c - single (3 : Fin 6) 4 (σ c)
    rw [sub_eq_add_neg, ← Matrix.single_neg, hσθ]
  · refine Subtype.ext (Units.ext ?_)
    refine (coe_iota4SL_usbSL_lower hθ hμ0 c).trans ?_
    show _ = ((iota3SL σ (blockSL E 3 2 1 _ (Matrix.SpecialLinearGroup.transvection hab c)) :
      SL(6, E)) : Matrix (Fin 6) (Fin 6) E)
    rw [blockSL_three_transvection, coe_iota3SL_transvection]
    unfold rootMatrix
    show 1 + single (2 : Fin 6) 1 c + single (4 : Fin 6) 3 (-θ c) =
      1 + single (2 : Fin 6) 1 c - single (4 : Fin 6) 3 (σ c)
    rw [sub_eq_add_neg, ← Matrix.single_neg, hσθ]
  · exact absurd rfl hab

include hσ hθ hμ0 hμ hσθ in
theorem iota4_usb_range :
    ((usb θ hθ).range).map (iota4 hθ hμ0 hμ hσθ) = (B23 E).map (iota3 hσ) := by
  rw [← MonoidHom.range_comp, iota4_comp_usb hσ hθ hμ0 hμ hσθ, MonoidHom.range_comp]
  rfl

end Cons

section Inj
variable {E : Type} [Field E]

theorem toGL_injective_SL {n : ℕ} :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(n, E) →* GL (Fin n) E) :=
  fun _ _ h => Subtype.ext (congrArg (fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E)) h)

theorem mul_blockMat_apply_of_not_mem_right {m k i : ℕ} (A : Matrix (Fin m) (Fin m) E)
    (B : Matrix (Fin k) (Fin k) E) (a : Fin m) {b : Fin m} (hb : ¬ (i ≤ b.val ∧ b.val < i + k)) :
    (A * blockMat m i B) a b = A a b := by
  have h : ∀ x : Fin m, blockMat m i B x b = (1 : Matrix (Fin m) (Fin m) E) x b :=
    fun x => blockMat_apply_of_not_mem_right B x hb
  have h2 : (A * blockMat m i B) a b = ∑ x, A a x * blockMat m i B x b := rfl
  rw [h2]
  simp only [h]
  have h3 : (A * (1 : Matrix (Fin m) (Fin m) E)) a b =
      ∑ x, A a x * (1 : Matrix (Fin m) (Fin m) E) x b := rfl
  rw [← h3, Matrix.mul_one]

theorem iota3SL_injective (ψ : E ≃+* E) : Function.Injective (iota3SL ψ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := congrArg (fun x : SL(6, E) => (x : Matrix (Fin 6) (Fin 6) E)) hg
  simp only [iota3SL_apply, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL,
    Matrix.SpecialLinearGroup.coe_one] at h
  refine Subtype.ext (Matrix.ext fun x y => ?_)
  have hx := congrFun (congrFun h (blockIdx 0 (by norm_num) x)) (blockIdx 0 (by norm_num) y)
  rw [mul_blockMat_apply_of_not_mem_right _ _ _ (by
    simp only [blockIdx_val]; have := y.isLt; omega), blockMat_apply_blockIdx] at hx
  rw [hx]
  simp [Matrix.one_apply, blockIdx, Fin.ext_iff]


theorem iota4SL_injective {μ : E} (hμ0 : μ ≠ 0) : Function.Injective (iota4SL μ hμ0) :=
  (blockSL_injective (K := E) (m := 6) (k := 4) (i := 1) (by norm_num)).comp
    (conjSL (Dm μ) (Dinv μ) (Dm_mul_Dinv hμ0)).injective

end Inj

section InjSU
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {θ : E →+* E}
  (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

include hσ in
theorem iota3_injective : Function.Injective (iota3 hσ) := fun _ _ h =>
  iota3SL_injective σ (toGL_injective_SL (congrArg Subtype.val h))

include hθ hμ0 hμ hσθ in
theorem iota4_injective : Function.Injective (iota4 hθ hμ0 hμ hσθ) := fun _ _ h =>
  Subtype.ext (iota4SL_injective hμ0 (toGL_injective_SL (congrArg Subtype.val h)))

end InjSU

section Comm
variable {E : Type} [Field E]

theorem commute_of_closure {G H K : Type*} [Group G] [Group H] [Group K] (f : G →* K)
    (g : H →* K) {S : Set G} {T : Set H} (hS : Subgroup.closure S = ⊤)
    (hT : Subgroup.closure T = ⊤) (h : ∀ s ∈ S, ∀ t ∈ T, Commute (f s) (g t)) (x : G) (y : H) :
    Commute (f x) (g y) := by
  have h1 : ∀ t ∈ T, ∀ x : G, Commute (f x) (g t) := by
    intro t ht x
    have hx : x ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top x
    have : x ∈ (Subgroup.centralizer ({g t} : Set K)).comap f := by
      refine (Subgroup.closure_le _).mpr ?_ hx
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h s hs t ht)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this)
  have hy : y ∈ Subgroup.closure T := by rw [hT]; exact Subgroup.mem_top y
  have : y ∈ (Subgroup.centralizer ({f x} : Set K)).comap g := by
    refine (Subgroup.closure_le _).mpr ?_ hy
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h1 t ht x).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm

theorem commute_longRootMatrix_rootMatrix {σ : E ≃+* E} {n : ℕ} {i a b : Fin n}
    (hia' : a ≠ Fin.rev i) (hib : b ≠ i) (t d : E) :
    longRootMatrix i t * rootMatrix σ a b d = rootMatrix σ a b d * longRootMatrix i t := by
  have e1 : (single i (Fin.rev i) t : Matrix (Fin n) (Fin n) E) * single a b d = 0 :=
    Matrix.single_mul_single_of_ne t i (Fin.rev i) a (Ne.symm hia') d
  have e2 : (single i (Fin.rev i) t : Matrix (Fin n) (Fin n) E) *
      single (Fin.rev b) (Fin.rev a) (σ d) = 0 :=
    Matrix.single_mul_single_of_ne t i (Fin.rev i) (Fin.rev b)
      (fun h => hib (Fin.rev_injective h).symm) _
  have e3 : (single a b d : Matrix (Fin n) (Fin n) E) * single i (Fin.rev i) t = 0 :=
    Matrix.single_mul_single_of_ne d a b i hib t
  have e4 : (single (Fin.rev b) (Fin.rev a) (σ d) : Matrix (Fin n) (Fin n) E) *
      single i (Fin.rev i) t = 0 :=
    Matrix.single_mul_single_of_ne (σ d) (Fin.rev b) (Fin.rev a) i
      (fun h => hia' (by rw [← h, Fin.rev_rev])) t
  unfold longRootMatrix rootMatrix
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, e1, e2, e3, e4]
  abel


theorem commute_longRootHom_rootHom {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {i a b : Fin n} (hi : i ≠ Fin.rev i) (hab : a ≠ b) (ha : a ≠ Fin.rev a) (hb : b ≠ Fin.rev b)
    (h1 : a ≠ Fin.rev i) (h2 : b ≠ i) (c : Multiplicative (traceZero σ)) (d : Multiplicative E) :
    Commute (longRootHom σ hi c) (rootHom σ hσ hab ha hb d) :=
  Subtype.ext (Units.ext (commute_longRootMatrix_rootMatrix h1 h2 _ _))

end Comm

section CommNodes
variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c) {θ : E →+* E}
  (hθ : ∀ c, θ (θ c) = c) {μ : E} (hμ0 : μ ≠ 0) (hμ : σ μ = -μ) (hσθ : ∀ c, σ c = θ c)

include hσ hθ hμ0 hμ hσθ in
theorem commutes_node2_node0 : Commutes (nodeSU hσ 2) (nodeSU hσ 0) := by
  have hle2 := iota4_ulb_le hσ hθ hμ0 hμ hσθ
  have hge2 := iota4_ulb_ge hσ hθ hμ0 hμ hσθ
  have hle0 := iota3_B12_le hσ
  have hge0 := iota3_B12_ge hσ
  have e2 : nodeSU hσ 2 = ((ulb θ hθ).range).map (iota4 hθ hμ0 hμ hσθ) := le_antisymm hge2 hle2
  have e0 : nodeSU hσ 0 = (B12 E).map (iota3 hσ) := le_antisymm hge0 hle0
  rw [e2, e0]
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
  have key := commute_of_closure ((iota4 hθ hμ0 hμ hσθ).comp (ulb θ hθ))
    ((iota3 hσ).comp (blockSL E 3 2 0 (by norm_num)))
    (CFSG.LinearGroups.special_linear_elementary_generation (K := fixedField θ) (n := 2))
    (CFSG.LinearGroups.special_linear_elementary_generation (K := E) (n := 2))
    (by
      rintro _ ⟨a, b, hab, s, rfl⟩ _ ⟨a', b', hab', t, rfl⟩
      show Commute (iota4 hθ hμ0 hμ hσθ (ulb θ hθ (Matrix.SpecialLinearGroup.transvection hab s)))
        (iota3 hσ (blockSL E 3 2 0 _ (Matrix.SpecialLinearGroup.transvection hab' t)))
      rw [iota3_blockSL_transvection hσ]
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b'
      all_goals first
        | exact absurd rfl hab
        | exact absurd rfl hab'
        | skip
      · rw [iota4_ulb_upper hθ hμ0 hμ hσθ]
        exact commute_longRootHom_rootHom hσ _ _ _ _ (by decide +kernel) (by decide +kernel) _ _
      · rw [iota4_ulb_upper hθ hμ0 hμ hσθ]
        exact commute_longRootHom_rootHom hσ _ _ _ _ (by decide +kernel) (by decide +kernel) _ _
      · rw [iota4_ulb_lower hθ hμ0 hμ hσθ]
        exact commute_longRootHom_rootHom hσ _ _ _ _ (by decide +kernel) (by decide +kernel) _ _
      · rw [iota4_ulb_lower hθ hμ0 hμ hσθ]
        exact commute_longRootHom_rootHom hσ _ _ _ _ (by decide +kernel)
          (by decide +kernel) _ _) A B
  exact key.eq

end CommNodes

section Gen
variable {p f : ℕ} [Fact p.Prime] {E : Type} [Field E] [Finite E] [CharP E p]

theorem nodes_generate (hF : Nat.card E = (p ^ f) ^ 2) :
    nodeSU (unitaryInvolution_involutive (K := E) (p := p) (f := f) hF) 2 ⊔
      nodeSU (unitaryInvolution_involutive (K := E) (p := p) (f := f) hF) 1 ⊔
        nodeSU (unitaryInvolution_involutive (K := E) (p := p) (f := f) hF) 0 = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hCT := isCTGroupDatum hF 6 (by norm_num) ζ hζ
  have h := iSup_rankOne_eq_top_of_ct (D := rootDatum hF 6) hCT (by
    simp [rootDatum, divisible, show Even (6 : ℕ) by decide]
    rfl)
  rw [eq_top_iff, ← h]
  refine iSup_le fun k => ?_
  fin_cases k
  · exact le_sup_of_le_right (le_refl _)
  · exact le_sup_of_le_left (le_sup_of_le_right (le_refl _))
  · exact le_sup_of_le_left (le_sup_of_le_left (le_refl _))

end Gen

section Center
variable {E : Type} [Field E]

theorem eq_one_of_mem_B23_commute_B12 {b : SL(3, E)} (hb : b ∈ B23 E)
    (h₁ : ∀ c : E, Commute b (blockSL E 3 2 0 (by norm_num)
      (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) c)))
    (h₂ : ∀ c : E, Commute b (blockSL E 3 2 0 (by norm_num)
      (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) c))) :
    b = 1 := by
  obtain ⟨A, rfl⟩ := hb
  have e1 := congrArg (fun x : SL(3, E) => (x : Matrix (Fin 3) (Fin 3) E)) (h₁ 1).eq
  have e2 := congrArg (fun x : SL(3, E) => (x : Matrix (Fin 3) (Fin 3) E)) (h₂ 1).eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, CFSG.LinearGroups.coe_transvection,
    blockMat_one_add_single (s := 0) (k := 2) (m := 3) (by norm_num)] at e1 e2
  have a00 := congrFun (congrFun e1 0) 1
  have a01 := congrFun (congrFun e1 0) 2
  have a10 := congrFun (congrFun e2 1) 0
  have a02 := congrFun (congrFun e2 2) 0
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.mul_apply, Fin.sum_univ_three, blockMat_apply, Matrix.single_apply,
    Matrix.one_apply] at a00 a01 a10 a02
  have h00 : (A : Matrix (Fin 2) (Fin 2) E) 0 0 = 1 := a00.symm
  have h01 : (A : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := a01.symm
  have h10 : (A : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := a02
  have h11 : (A : Matrix (Fin 2) (Fin 2) E) 1 1 = 1 := by
    rw [h00, h01] at hdet
    simpa using hdet
  have hA : A = 1 := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11])
  rw [hA, map_one]

end Center

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem nonempty_su6Frame (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Nonempty (SU6Frame p f hf) := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f) hF
  obtain ⟨μ, hμ0, hμ⟩ := exists_unitaryInvolution_eq_neg (K := GaloisField p (2 * f)) (p := p)
    (f := f) hF
  have hσθ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = frobQ p f c := fun c => by
    rw [unitaryInvolution_apply, frobQ_apply]
  have hθ := frobQ_frobQ p f hf
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 6
  let φ := conjEquiv P hP
  obtain ⟨i₀, hi₀⟩ : ∃ i, IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6)
      ((nodeSU hσ 2).map φ.toMonoidHom) i :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hF hp2 (by norm_num)
      (k := ⟨2, by norm_num⟩) (γ := Pi.single 2 1) (by decide +kernel) (by decide +kernel) P hP
  have hB23 : nodeSU hσ 1 = (WeakCT.B23 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B23_ge hσ) (iota3_B23_le hσ)
  have hB12 : nodeSU hσ 0 = (WeakCT.B12 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B12_ge hσ) (iota3_B12_le hσ)
  have hlb : nodeSU hσ 2 = ((ulb (frobQ p f) hθ).range).map (iota4 hθ hμ0 hμ hσθ) :=
    le_antisymm (iota4_ulb_ge hσ hθ hμ0 hμ hσθ) (iota4_ulb_le hσ hθ hμ0 hμ hσθ)
  have hker : (QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * f)) p f 6))).ker ≤
      Subgroup.center (Su (GaloisField p (2 * f)) p f 6) := by
    rw [QuotientGroup.ker_mk']
  refine ⟨{
    R₁ := (nodeSU hσ 2).map φ.toMonoidHom
    S₂ := (nodeSU hσ 1).map φ.toMonoidHom
    S₃ := (nodeSU hσ 0).map φ.toMonoidHom
    R₁_mem := ⟨i₀, hi₀⟩
    commutes_R₁_S₃ := ?_
    gen := ?_
    ι₄ := φ.toMonoidHom.comp (iota4 hθ hμ0 hμ hσθ)
    ι₄_injective := φ.injective.comp (iota4_injective hθ hμ0 hμ hσθ)
    ι₄_long := ?_
    ι₄_short := ?_
    ι₃ := φ.toMonoidHom.comp (iota3 hσ)
    ι₃_injective := φ.injective.comp (iota3_injective hσ)
    ι₃_B23 := ?_
    ι₃_B12 := ?_
    R₁_center := ?_
    S₂_center := ?_ }⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, commutes_node2_node0 hσ hθ hμ0 hμ hσθ x hx y hy]
  · rw [← Subgroup.map_sup, ← Subgroup.map_sup, nodes_generate hF]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom) hlb.symm
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom)
      ((iota4_usb_range hσ hθ hμ0 hμ hσθ).trans hB23.symm)
  · rw [← Subgroup.map_map, ← hB23]
  · rw [← Subgroup.map_map, ← hB12]
  · exact fun r hr hc => CFSG.ClassicalInvolution.Models.Transfer.eq_one_of_mem_ker_of_isLongRootSU2
      hF hp2 hq (by norm_num) hi₀ hker r hr (by rw [QuotientGroup.ker_mk']; exact hc)
  · rintro _ ⟨x, hx, rfl⟩ hc
    rw [hB23] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hcx : ∀ y : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 6,
        iota3 hσ b * y = y * iota3 hσ b := fun y =>
      φ.injective (by rw [map_mul, map_mul]; exact ((Subgroup.mem_center_iff.mp hc) (φ y)).symm)
    have hb1 : b = 1 := by
      refine eq_one_of_mem_B23_commute_B12 hb (fun c => ?_) (fun c => ?_)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
    rw [hb1, map_one, map_one]

end Final

end CFSG.ClassicalInvolution.RouteD
