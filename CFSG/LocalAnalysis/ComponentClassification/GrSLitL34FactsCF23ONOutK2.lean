module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK1Sigma
public import Certificates.Certificate22232

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.F3.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier
open scoped Matrix

theorem kernel_check :
    (okRows rRows && (mulVecRow wRows vVec).beq V.zero &&
      eqM 154 (addM (mul 154 rRows wRows) (outerRows vVec uVec)) (idM 154)) = true :=
  Certificates.certificate22232.1

theorem spin_check :
    (spinRows.size == 154 && spinRows[0]!.beq vVec &&
      (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
        decide (spinLab[t + 1]! < 2) &&
        spinRows[t + 1]!.beq (mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]!)) &&
      okRows spinInvRows && eqM 154 (mul 154 spinInvRows spinRows) (idM 154)) = true :=
  Certificates.certificate22232.2.1

theorem sq_neg_check : eqM 154 n0SqRows negIdRows = true :=
  Certificates.certificate22232.2.2

@[expose] def vecOf (x : V) : Fin 154 → ZMod 3 := fun j => x.val j

theorem vecOf_eq_of_beq {x y : V} (h : x.beq y = true) : vecOf x = vecOf y :=
  funext fun j => V.val_ext h j

theorem rowsWF_addM {X Y : Array V} (hX : RowsWF X) (hY : RowsWF Y) : RowsWF (addM X Y) := by
  intro j
  unfold addM
  by_cases hj : j < 154
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact V.wf_add (hX j) (hY j)
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact V.wf_zero

theorem toMat_addM {X Y : Array V} (hX : RowsWF X) (hY : RowsWF Y) :
    toMat 154 (addM X Y) = toMat 154 X + toMat 154 Y := by
  ext i j
  rw [Matrix.add_apply, toMat_apply, toMat_apply, toMat_apply, addM,
    getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  exact V.val_add (hX i) (hY i) j

theorem rowsWF_negM {X : Array V} (hX : RowsWF X) : RowsWF (negM X) := by
  intro j
  unfold negM
  by_cases hj : j < X.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map]
    have := hX j
    rw [getElem!_pos X j hj] at this
    exact V.wf_neg this
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact V.wf_zero

theorem toMat_negM {X : Array V} (hX : RowsWF X) (hs : X.size = 154) :
    toMat 154 (negM X) = -toMat 154 X := by
  ext i j
  rw [Matrix.neg_apply, toMat_apply, toMat_apply, negM,
    getElem!_pos _ _ (by simp [hs]), Array.getElem_map]
  have := hX i
  rw [getElem!_pos X (i : ℕ) (by rw [hs]; exact i.isLt)] at this ⊢
  exact V.val_neg _ j this

theorem rowsWF_transpose' (X : Array V) : ∀ j : ℕ, (transpose 154 X)[j]!.wf = true :=
  RowsWF.transpose 154 X

theorem vecOf_mulVecRow {M : Array V} {x : V} (hx : x.wf = true) :
    vecOf (mulVecRow M x) = toMat 154 M *ᵥ vecOf x := by
  funext k
  rw [vecOf, mulVecRow, V.val_comb 154 _ x (rowsWF_transpose' M) hx k, Matrix.mulVec,
    dotProduct, Finset.sum_range (fun j => x.val j * (transpose 154 M)[j]!.val k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun (toMat_transpose (d := 154) M) j) k
  rw [Matrix.transpose_apply, toMat_apply, toMat_apply] at h
  rw [h, vecOf, mul_comm, toMat_apply]

theorem wf_mulVecRow (M : Array V) {x : V} (hx : x.wf = true) : (mulVecRow M x).wf = true :=
  V.wf_comb 154 _ x (rowsWF_transpose' M) hx

theorem V.get_lt_three (a : V) (j : ℕ) : a.get j < 3 := by
  unfold V.get
  split_ifs <;> norm_num

theorem V.val_eq_get (a : V) (j : ℕ) : a.val j = (a.get j : ZMod 3) := rfl

theorem toMat_outerRows {v u : V} (hu : u.wf = true) (i j : Fin 154) :
    toMat 154 (outerRows v u) i j = v.val i * u.val j := by
  rw [toMat_apply, outerRows, getElem!_pos _ _ (by simp), Array.getElem_ofFn, V.val_eq_get v i]
  have hlt := V.get_lt_three v i
  by_cases h1 : v.get i = 1
  · rw [ite_eq_left h1, h1]
    simp
  · rw [ite_eq_right h1]
    by_cases h2 : v.get i = 2
    · rw [ite_eq_left h2, h2, V.val_neg u j hu]
      have h3 : ((2 : ℕ) : ZMod 3) = -1 := by decide
      rw [h3]
      exact (neg_one_mul _).symm

    · rw [ite_eq_right h2, V.val_zero, show v.get i = 0 by omega]
      simp

theorem wf_vecOfCode (s : String) : (vecOfCode s).wf = true := V.wf_ofFn _ _

theorem rowsWF_wRows : RowsWF wRows :=
  rowsWF_addM (rowsWF_addM (RowsWF.idM 154) (RowsWF.mul _ 154 rowsWF_rowsA rowsWF_rowsB))
    (rowsWF_negM (RowsWF.mul _ 154 (RowsWF.mul _ 154 rowsWF_rowsA rowsWF_rowsB) rowsWF_rowsB))

theorem toMat_wRows : toMat 154 wRows = 1 + mA * mB + -(mA * mB * mB) := by
  have hAB := RowsWF.mul rowsA 154 rowsWF_rowsA rowsWF_rowsB
  rw [wRows, toMat_addM (rowsWF_addM (RowsWF.idM 154) hAB)
    (rowsWF_negM (RowsWF.mul _ 154 hAB rowsWF_rowsB)),
    toMat_addM (RowsWF.idM 154) hAB, toMat_idM,
    toMat_negM (RowsWF.mul _ 154 hAB rowsWF_rowsB) (by rw [size_mul, size_mul, rowsA_size']),
    toMat_mul' (by rw [size_mul, rowsA_size']) hAB rowsWF_rowsB,
    toMat_mul' rowsA_size' rowsWF_rowsA rowsWF_rowsB, toMat_rowsA, toMat_rowsB]

theorem kernel_spec {x : Fin 154 → ZMod 3}
    (hx : toMat 154 wRows *ᵥ x = 0) : x = (vecOf uVec ⬝ᵥ x) • vecOf vVec := by
  have hc := kernel_check
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hR, -⟩, hRW⟩ := hc
  have hmat := toMat_eq_of_eqM hRW
  rw [toMat_addM (RowsWF.mul _ 154 (rowsWF_of_okRows hR) rowsWF_wRows)
      (fun j => by
        unfold outerRows
        by_cases hj : j < 154
        · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
          split_ifs
          · exact wf_vecOfCode _
          · exact V.wf_neg (wf_vecOfCode _)
          · exact V.wf_zero
        · rw [getElem!_neg _ j (by simpa using hj)]
          exact V.wf_zero),
    toMat_mul' (size_of_okRows hR) (rowsWF_of_okRows hR) rowsWF_wRows, toMat_idM] at hmat
  have e := congrArg (fun T => T *ᵥ x) hmat
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, zero_add,
    Matrix.one_mulVec] at e
  refine e.symm.trans ?_
  funext i
  rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toMat_outerRows (v := vVec) (u := uVec) (wf_vecOfCode uCode) i j, vecOf, vecOf]
  ring

@[expose] def spinVec (t : ℕ) : Fin 154 → ZMod 3 := vecOf spinRows[t]!

theorem wf_of_beq {a b : V} (h : a.beq b = true) (hb : b.wf = true) : a.wf = true := by
  obtain ⟨hp, hm⟩ := V.beq_iff.1 h
  unfold V.wf at hb ⊢
  rw [hp, hm]
  exact hb

theorem spin_facts :
    spinVec 0 = vecOf vVec ∧
      (∀ t, 1 ≤ t → t < 154 → spinPar[t]! < t ∧
        (spinVec t = mA *ᵥ spinVec spinPar[t]! ∨ spinVec t = mB *ᵥ spinVec spinPar[t]!)) ∧
      toMat 154 spinInvRows * toMat 154 spinRows = 1 := by
  have hc := spin_check
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hsz, h0⟩, hall⟩, hok⟩, heq⟩ := hc
  have hstep : ∀ t, 1 ≤ t → t < 154 → spinPar[t]! < t ∧ spinLab[t]! < 2 ∧
      spinRows[t]!.beq (mulVecRow (spinGen spinLab[t]!) spinRows[spinPar[t]!]!) = true := by
    intro t h1 h2
    obtain ⟨⟨a, b⟩, c⟩ := hall (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at a b c
    exact ⟨a, b, c⟩
  have hwf : ∀ t : ℕ, (spinRows[t]! : V).wf = true := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < 154
      · rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact wf_of_beq h0 (wf_vecOfCode vCode)
        · obtain ⟨hp, -, hb⟩ := hstep t hpos ht
          exact wf_of_beq hb (wf_mulVecRow _ (ih _ hp))
      · rw [getElem!_neg _ t (by omega)]
        exact V.wf_zero
  refine ⟨vecOf_eq_of_beq h0, fun t h1 h2 => ?_, ?_⟩
  · obtain ⟨hp, hl, hb⟩ := hstep t h1 h2
    refine ⟨hp, ?_⟩
    have e : spinVec t = toMat 154 (spinGen spinLab[t]!) *ᵥ spinVec spinPar[t]! := by
      rw [spinVec, vecOf_eq_of_beq hb, vecOf_mulVecRow (hwf _)]
      rfl
    rcases (by omega : spinLab[t]! = 0 ∨ spinLab[t]! = 1) with h | h
    · left
      rw [e, spinGen, ite_eq_left h, toMat_rowsA]
    · right
      rw [e, spinGen, ite_eq_right (by omega), toMat_rowsB]
  · have e := toMat_eq_of_eqM heq
    rwa [toMat_mul' (size_of_okRows hok) (rowsWF_of_okRows hok) (fun j => hwf j), toMat_idM]
      at e

theorem comm_peak {R : Type*} [Ring R] {Y A B : R} (hA : Y * A = A * Y) (hB : Y * B = B * Y) :
    Y * (1 + A * B + -(A * B * B)) = (1 + A * B + -(A * B * B)) * Y := by
  have hAB : Y * (A * B) = A * B * Y := by
    rw [← mul_assoc, hA, mul_assoc, hB, mul_assoc]
  have hABB : Y * (A * B * B) = A * B * B * Y := by
    calc Y * (A * B * B) = Y * (A * B) * B := by simp only [mul_assoc]
      _ = A * B * Y * B := by rw [hAB]
      _ = A * B * (Y * B) := by simp only [mul_assoc]
      _ = A * B * (B * Y) := by rw [hB]
      _ = A * B * B * Y := by simp only [mul_assoc]
  rw [mul_add, mul_add, mul_one, hAB, mul_neg, hABB, add_mul, add_mul, one_mul, neg_mul]

theorem commutant_scalar {Y : Matrix (Fin 154) (Fin 154) (ZMod 3)}
    (hA : Y * mA = mA * Y) (hB : Y * mB = mB * Y) : ∃ μ : ZMod 3, Y = μ • 1 := by
  obtain ⟨h0, hstep, hXU⟩ := spin_facts
  set v := vecOf vVec with hv
  set μ := vecOf uVec ⬝ᵥ (Y *ᵥ v) with hμ
  have hW : Y * toMat 154 wRows = toMat 154 wRows * Y := by
    rw [toMat_wRows]
    exact comm_peak hA hB
  have hWv : toMat 154 wRows *ᵥ v = 0 := by
    have hc := kernel_check
    simp only [Bool.and_eq_true] at hc
    have e := vecOf_eq_of_beq hc.1.2
    rw [vecOf_mulVecRow (x := vVec) (wf_vecOfCode vCode)] at e
    rw [hv, e]
    funext j
    exact V.val_zero j
  have hYv : Y *ᵥ v = μ • v := by
    refine kernel_spec ?_
    rw [Matrix.mulVec_mulVec, ← hW, ← Matrix.mulVec_mulVec, hWv, Matrix.mulVec_zero]
  have hspin : ∀ t, t < 154 → Y *ᵥ spinVec t = μ • spinVec t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · rw [h0]
        exact hYv
      · obtain ⟨hp, hst | hst⟩ := hstep t hpos ht
        · rw [hst, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ih _ hp (by omega),
            Matrix.mulVec_smul]
        · rw [hst, Matrix.mulVec_mulVec, hB, ← Matrix.mulVec_mulVec, ih _ hp (by omega),
            Matrix.mulVec_smul]
  refine ⟨μ, eq_smul_one_of_rows hXU μ fun t => ?_⟩
  have hrow : (toMat 154 spinRows) t = spinVec t := by
    funext j
    rfl
  rw [hrow]
  exact hspin t t.isLt

theorem toMat_n0Sq :
    toMat 154 n0Rows * toMat 154 n0Rows = -1 := by
  obtain ⟨h1, h2, -⟩ := n0_facts
  have e := toMat_eq_of_eqM sq_neg_check
  rw [n0SqRows, toMat_mul' h1 h2 h2, negIdRows,
    toMat_negM (RowsWF.idM 154) size_idM, toMat_idM] at e
  exact e

theorem zmod3_sq_eq_one : ∀ μ : ZMod 3, μ ≠ 0 → μ * μ = 1 := by decide

theorem comm_of_conj_eq {R : Type*} [Ring R] {N Ninv G Ginv X : R} (hN : Ninv * N = 1)
    (hG : Ginv * G = 1) (h : N * X * Ninv = G * X * Ginv) : Ginv * N * X = X * (Ginv * N) := by
  calc Ginv * N * X = Ginv * (N * X * Ninv) * N := by simp only [mul_assoc, hN, mul_one]
    _ = Ginv * (G * X * Ginv) * N := by rw [h]
    _ = X * (Ginv * N) := by
        simp only [mul_assoc]
        rw [← mul_assoc Ginv G, hG, one_mul]

theorem sigmaJ_ne_conj (g : J) :
    sigmaJ ≠ MulAut.conj g := by
  intro h
  have hcomm : ∀ x : J, mat g⁻¹ * toMat 154 n0Rows * mat x =
      mat x * (mat g⁻¹ * toMat 154 n0Rows) := by
    intro x
    have hx := congrArg (fun φ : MulAut J => mat (φ x)) h
    simp only [MulAut.conj_apply] at hx
    rw [mat_sigmaJ, mat_mul, mat_mul] at hx
    have hinv : toMat 154 n0InvRows * toMat 154 n0Rows = 1 :=
      ONSchreier.mul_eq_one_symm n0_facts.2.2.2.2
    have hg : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
    exact comm_of_conj_eq (R := Matrix (Fin 154) (Fin 154) (ZMod 3)) (N := toMat 154 n0Rows)
      (Ninv := toMat 154 n0InvRows) (G := mat g) (Ginv := mat g⁻¹) (X := mat x) hinv hg hx
  have hA' := hcomm ga
  have hB' := hcomm gb
  rw [mat_ga] at hA'
  rw [mat_gb] at hB'
  obtain ⟨μ, hμ⟩ := commutant_scalar hA' hB'
  have hN : toMat 154 n0Rows = μ • mat g := by
    calc toMat 154 n0Rows = mat g * (mat g⁻¹ * toMat 154 n0Rows) := by
          rw [← mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, one_mul]
      _ = μ • mat g := by rw [hμ, Matrix.mul_smul, mul_one]
  have hsq := toMat_n0Sq
  rw [hN, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mat_mul] at hsq
  by_cases hμ0 : μ = 0
  · rw [hμ0, zero_mul, zero_smul] at hsq
    have h00 := congrFun (congrFun hsq 0) 0
    rw [Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact absurd h00 (by decide)
  · rw [zmod3_sq_eq_one μ hμ0, one_smul] at hsq
    exact mat_ne_neg_one (g * g) hsq

theorem sigmaPv_not_inner :
    sigmaPv ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
  rintro ⟨p, hp⟩
  apply sigmaJ_ne_conj (jEquivPv.symm p)
  refine MulEquiv.ext fun x => ?_
  have h1 : sigmaPv (jEquivPv x) = jEquivPv (sigmaJ x) := by
    rw [sigmaPv_apply, MulEquiv.symm_apply_apply]
  have h2 : sigmaPv (jEquivPv x) = p * jEquivPv x * p⁻¹ := by
    rw [← hp]
    rfl
  rw [MulAut.conj_apply, ← MulEquiv.symm_apply_apply jEquivPv (sigmaJ x), ← h1, h2, map_mul,
    map_mul, map_inv, MulEquiv.symm_apply_apply]

end CFSG.ComponentClassification.SolMax.ONOut
