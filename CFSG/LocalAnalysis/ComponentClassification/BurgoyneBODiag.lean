module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSliceR

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

@[expose] def vecEmbed4 (_hd : 4 ≤ d) (v : Fin 4 → K) : Fin d → K :=
  fun i => if h : (i : ℕ) < 4 then v ⟨i, h⟩ else 0

@[expose] def vecRestr4 (hd : 4 ≤ d) (x : Fin d → K) : Fin 4 → K := fun j => x ⟨j, by omega⟩

theorem vecEmbed4_apply_e4_inl (hd : 4 ≤ d) (v : Fin 4 → K) (j : Fin 4) :
    vecEmbed4 hd v (e4 hd (.inl j)) = v j := by
  rw [e4_inl]
  simp [vecEmbed4]

theorem vecEmbed4_apply_e4_inr (hd : 4 ≤ d) (v : Fin 4 → K) (k : Fin (d - 4)) :
    vecEmbed4 hd v (e4 hd (.inr k)) = 0 := by
  rw [e4_inr]
  simp [vecEmbed4]

theorem sum_mul_vecEmbed4 (hd : 4 ≤ d) (f : Fin d → K) (u : Fin 4 → K) :
    ∑ i, f i * vecEmbed4 hd u i = ∑ j : Fin 4, f ⟨j, by omega⟩ * u j := by
  rw [← (e4 hd).sum_comp, Fintype.sum_sum_type]
  simp only [vecEmbed4_apply_e4_inl, vecEmbed4_apply_e4_inr, mul_zero, Finset.sum_const_zero,
    add_zero]
  simp only [e4_inl]

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem polar_oQ_diag (x y : Fin d → K) :
    polar (oQ (diagGL hw)) x y = 2 * ∑ i, w i * x i * y i := by
  simp only [polar, oQ_apply, coe_diagGL, mulVec_diagonal, dotProduct, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  funext i
  ring

variable {hw} in
theorem polar_vecEmbed4 {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a) (x : Fin d → K)
    (u : Fin 4 → K) :
    polar (oQ (diagGL hw)) x (vecEmbed4 hd u) =
      2 * (α * (x ⟨0, by omega⟩ * u 0 + a * (x ⟨1, by omega⟩ * u 1) - x ⟨2, by omega⟩ * u 2 -
        a * (x ⟨3, by omega⟩ * u 3))) := by
  rw [polar_oQ_diag, sum_mul_vecEmbed4 hd]
  simp only [Fin.sum_univ_four]
  have h0 := hW.hw4 0
  have h1 := hW.hw4 1
  have h2 := hW.hw4 2
  have h3 := hW.hw4 3
  simp only [qW] at h0 h1 h2 h3
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, e3] at h0 h1 h2 h3 ⊢
  rw [h0, h1, h2, h3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

variable {hw} in
theorem Q_vecEmbed4 (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a)
    (u : Fin 4 → K) :
    oQ (diagGL hw) (vecEmbed4 hd u) =
      α * (u 0 * u 0 + a * (u 1 * u 1) - u 2 * u 2 - a * (u 3 * u 3)) := by
  have h := polar_self (oQ (diagGL hw)) (vecEmbed4 hd u)
  rw [polar_vecEmbed4 hW] at h
  have e : ∀ i (hi : i < 4), vecEmbed4 hd u ⟨i, by omega⟩ = u ⟨i, hi⟩ := fun i hi => by
    simp [vecEmbed4, hi]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)] at h
  rw [two_smul] at h
  apply mul_left_cancel₀ h2
  rw [two_mul, ← h]
  rfl

theorem Q_vecEmbed4_cons (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a)
    (u₀ u₁ u₂ u₃ : K) :
    oQ (diagGL hw) (vecEmbed4 hd ![u₀, u₁, u₂, u₃]) =
      α * (u₀ * u₀ + a * (u₁ * u₁) - u₂ * u₂ - a * (u₃ * u₃)) := by
  rw [Q_vecEmbed4 h2 hW]
  simp

theorem polar_vecEmbed4_cons {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a) (u₀ u₁ u₂ u₃ : K)
    (v₀ v₁ v₂ v₃ : K) :
    polar (oQ (diagGL hw)) (vecEmbed4 hd ![u₀, u₁, u₂, u₃]) (vecEmbed4 hd ![v₀, v₁, v₂, v₃]) =
      2 * (α * (u₀ * v₀ + a * (u₁ * v₁) - u₂ * v₂ - a * (u₃ * v₃))) := by
  rw [polar_vecEmbed4 hW]
  simp [vecEmbed4]

@[expose] def diagFrame (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a) :
    Frame (oQ (diagGL hw)) where
  P := ⟨vecEmbed4 hd ![1 / 2, 0, 1 / 2, 0], vecEmbed4 hd ![1 / (2 * α), 0, -1 / (2 * α), 0],
    by rw [Q_vecEmbed4_cons hw h2 hW]; ring, by rw [Q_vecEmbed4_cons hw h2 hW]; ring, by
      rw [polar_vecEmbed4_cons hw hW]
      field_simp [hW.hα]
      ring⟩
  P' := ⟨vecEmbed4 hd ![0, -1 / (2 * a), 0, 1 / (2 * a)],
    vecEmbed4 hd ![0, -1 / (2 * α), 0, -1 / (2 * α)],
    by rw [Q_vecEmbed4_cons hw h2 hW]; ring, by rw [Q_vecEmbed4_cons hw h2 hW]; ring, by
      rw [polar_vecEmbed4_cons hw hW]
      field_simp [hW.hα, hW.ha]
      ring⟩
  orth :=
    ⟨by rw [polar_vecEmbed4_cons hw hW]; ring, by rw [polar_vecEmbed4_cons hw hW]; ring,
      by rw [polar_vecEmbed4_cons hw hW]; ring, by rw [polar_vecEmbed4_cons hw hW]; ring⟩

theorem diagFrame_coords (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a)
    (x : Fin d → K) :
    (diagFrame hw h2 hW).coords x =
      ((dGL (Units.mk0 α hW.hα) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        qMat a (vecRestr4 hd x) := by
  rw [Frame.coords_apply, coe_dGL]
  change !![polar (oQ (diagGL hw)) x (vecEmbed4 hd ![1 / (2 * α), 0, -1 / (2 * α), 0]),
    -polar (oQ (diagGL hw)) x (vecEmbed4 hd ![0, -1 / (2 * α), 0, -1 / (2 * α)]);
    polar (oQ (diagGL hw)) x (vecEmbed4 hd ![0, -1 / (2 * a), 0, 1 / (2 * a)]),
    polar (oQ (diagGL hw)) x (vecEmbed4 hd ![1 / 2, 0, 1 / 2, 0])] = _
  simp only [polar_vecEmbed4 hW]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMat, vecRestr4, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hW.hα, hW.ha] <;> ring

theorem diagFrame_incl (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K} (hW : OSliceW hd w α a)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (diagFrame hw h2 hW).incl X =
      vecEmbed4 hd (qVec a ((((dGL (Units.mk0 α hW.hα))⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * X)) := by
  rw [Frame.incl_apply, coe_dGL_inv]
  change X 0 0 • vecEmbed4 hd ![1 / 2, 0, 1 / 2, 0] +
    X 1 1 • vecEmbed4 hd ![1 / (2 * α), 0, -1 / (2 * α), 0] +
    (-X 0 1) • vecEmbed4 hd ![0, -1 / (2 * a), 0, 1 / (2 * a)] +
    X 1 0 • vecEmbed4 hd ![0, -1 / (2 * α), 0, -1 / (2 * α)] = _
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, vecEmbed4, smul_eq_mul]
  by_cases hi : (i : ℕ) < 4
  · simp only [hi, ↓reduceDIte]
    obtain ⟨i, hi'⟩ := i
    simp only at hi
    interval_cases i <;>
      simp [qVec, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hW.hα, hW.ha] <;> ring
  · simp [hi]

theorem embed4_mulVec (hd : 4 ≤ d) (M : Matrix (Fin 4) (Fin 4) K) (x : Fin d → K) :
    embed4 K hd M *ᵥ x = x + vecEmbed4 hd (M *ᵥ vecRestr4 hd x - vecRestr4 hd x) := by
  funext i
  rw [embed4, coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm]
  simp only [Function.comp_apply, Pi.add_apply]
  have hx : (x ∘ e4 hd) ∘ Sum.inl = vecRestr4 hd x := by
    funext j
    simp only [Function.comp_apply, e4_inl]
    rfl
  rcases Nat.lt_or_ge (i : ℕ) 4 with hi | hi
  · rw [e4_symm_of_lt hd hi, fromBlocks_mulVec]
    simp only [Sum.elim_inl, zero_mulVec, add_zero]
    rw [hx]
    simp only [vecEmbed4, hi, ↓reduceDIte, Pi.sub_apply]
    have : x i = vecRestr4 hd x ⟨i, hi⟩ := rfl
    rw [this]
    ring
  · rw [e4_symm_of_ge hd hi, fromBlocks_mulVec]
    simp only [Sum.elim_inr, zero_mulVec, zero_add, one_mulVec, Function.comp_apply, e4_inr,
      vecEmbed4, show ¬ (i : ℕ) < 4 by omega, ↓reduceDIte, add_zero]
    congr 1
    ext
    simp
    omega

theorem diagFrame_La (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K}
    (hW : OSliceW hd w α a) (A : SL(2, K)) (x : Fin d → K) :
    (diagFrame hw h2 hW).La A x =
      (oSlice K h2 hd hW.ha (conjSL₂ (dGL (Units.mk0 α hW.hα))⁻¹ A) :
        Matrix (Fin d) (Fin d) K) *ᵥ x := by
  rw [Frame.La_apply, diagFrame_coords, diagFrame_incl, coe_oSlice, embed4_mulVec,
    qLamMat_mulVec, coe_conjSL₂, inv_inv]
  congr 2
  set D := ((dGL (Units.mk0 α hW.hα) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hD
  set Di := (((dGL (Units.mk0 α hW.hα))⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hDi
  set q := qMat a (vecRestr4 hd x) with hq
  have hDD : Di * D = 1 := by rw [hD, hDi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : Di * ((A : Matrix (Fin 2) (Fin 2) K) * (D * q) - D * q) =
      Di * (A : Matrix (Fin 2) (Fin 2) K) * D * q - q := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc Di D q, hDD, Matrix.one_mul,
      ← Matrix.mul_assoc]
  rw [e]
  change (qEquiv h2 hW.ha).symm (Di * (A : Matrix (Fin 2) (Fin 2) K) * D * q - q) = _
  rw [map_sub]
  congr 1
  change qVec a (qMat a (vecRestr4 hd x)) = vecRestr4 hd x
  exact qVec_qMat h2 hW.ha _

@[expose] def sigmaSL (A : SL(2, K)) : SL(2, K) :=
  ⟨sigmaLin (A : Matrix (Fin 2) (Fin 2) K), by rw [det_sigmaLin]; exact A.2⟩

omit [Field K] in
theorem coe_sigmaSL [Field K] (A : SL(2, K)) :
    ((sigmaSL A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = sigmaLin (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem diagFrame_swap_La (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} {α a : K}
    (hW : OSliceW hd w α a) (A : SL(2, K)) (x : Fin d → K) :
    (diagFrame hw h2 hW).swap.La A x =
      (oSliceR K h2 hd hW.ha (sigmaSL A)⁻¹ : Matrix (Fin d) (Fin d) K) *ᵥ x := by
  rw [Frame.La_swap_apply, Frame.embLin_apply, diagFrame_coords, diagFrame_incl, coe_oSliceR,
    embed4_mulVec]
  change x + _ = x + vecEmbed4 hd (qGamMat h2 hW.ha (rightMul (sigmaSL A)⁻¹) *ᵥ
    vecRestr4 hd x - vecRestr4 hd x)
  rw [qGamMat_mulVec, rightMul_apply, inv_inv, coe_sigmaSL]
  congr 2
  simp only [LinearMap.mulRight_apply]
  set D := ((dGL (Units.mk0 α hW.hα) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hD
  set Di := (((dGL (Units.mk0 α hW.hα))⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hDi
  set q := qMat a (vecRestr4 hd x) with hq
  have hDD : Di * D = 1 := by rw [hD, hDi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : Di * (D * q * sigmaLin (A : Matrix (Fin 2) (Fin 2) K) - D * q) =
      q * sigmaLin (A : Matrix (Fin 2) (Fin 2) K) - q := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  rw [e]
  change (qEquiv h2 hW.ha).symm (q * sigmaLin (A : Matrix (Fin 2) (Fin 2) K) - q) = _
  rw [map_sub]
  congr 1
  change qVec a (qMat a (vecRestr4 hd x)) = vecRestr4 hd x
  exact qVec_qMat h2 hW.ha _

theorem diagFrame_perp (h2 : (2 : K) ≠ 0) {hd : 4 ≤ d} (hd5 : 5 ≤ d) {α a : K}
    (hW : OSliceW hd w α a) :
    IsUnit (oQ (diagGL hw) (Pi.single ⟨4, by omega⟩ 1)) ∧
      polar (oQ (diagGL hw)) (diagFrame hw h2 hW).e₁ (Pi.single ⟨4, by omega⟩ 1) = 0 ∧
      polar (oQ (diagGL hw)) (diagFrame hw h2 hW).f₁ (Pi.single ⟨4, by omega⟩ 1) = 0 ∧
      polar (oQ (diagGL hw)) (diagFrame hw h2 hW).e₂ (Pi.single ⟨4, by omega⟩ 1) = 0 ∧
      polar (oQ (diagGL hw)) (diagFrame hw h2 hW).f₂ (Pi.single ⟨4, by omega⟩ 1) = 0 := by
  have hp : ∀ u : Fin 4 → K, polar (oQ (diagGL hw)) (vecEmbed4 hd u)
      (Pi.single ⟨4, by omega⟩ 1) = 0 := by
    intro u
    rw [polar_comm, polar_vecEmbed4 hW]
    simp [Fin.ext_iff]
  refine ⟨?_, hp _, hp _, hp _, hp _⟩
  rw [oQ_apply, coe_diagGL]
  simp only [mulVec_single]
  simp [hw]

end CFSG.ComponentClassification.Burgoyne.B
