module

public import Certificates.Data.Kernel.Misc.YamakiS0
public import Certificates.Data.YamakiZRig
public import CFSG.Certificates.Kernel.Misc.BfsEnumSound
public import CFSG.Certificates.Kernel.Misc.BfsKSound
public import CFSG.Certificates.Kernel.Sp62Pk.Sound

public section

namespace CFSG.KC.YamakiS0

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiS0 CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.Misc.Spec Matrix
open CFSG.KD.Sp62 (MULF ONE)

@[expose] def matN (N : ℕ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (pkMat 6 N).submatrix finSumFinEquiv finSumFinEquiv

@[expose] def arrN (N : ℕ) : Array ℕ := matArr (matN N)

theorem compA_matArr (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    compA (matArr A) (matArr B) = matArr (A * B) := by
  refine ext64 (size_compA _ _) (size_matArr _) fun i hi => ?_
  rw [compA_get _ _ hi, matArr_get B hi, matArr_get A (codeOf_lt _), vecOf_codeOf,
    matArr_get _ hi, ← mulVec_mulVec]

theorem matArr_inj {A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (h : matArr A = matArr B) : A = B := by
  rw [ext_iff_mulVec]
  intro v
  have hv : (matArr A)[codeOf v]! = (matArr B)[codeOf v]! := by rw [h]
  rw [matArr_get A (codeOf_lt v), matArr_get B (codeOf_lt v), vecOf_codeOf] at hv
  rw [← vecOf_codeOf (A *ᵥ v), hv, vecOf_codeOf]

theorem matN_mul (A B : ℕ) : matN (MULF A B) = matN A * matN B := by
  unfold matN
  rw [CFSG.KC.Sp62.pkMat_MULF]
  rw [Matrix.submatrix_mul_equiv]

theorem arrN_mul (A B : ℕ) : compA (arrN A) (arrN B) = arrN (MULF A B) := by
  unfold arrN
  rw [compA_matArr, matN_mul]

theorem arrN_inj {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) (h : arrN A = arrN B) : A = B := by
  have hm := matArr_inj h
  apply CFSG.KC.Sp62.pkMat_inj hA hB
  ext i j
  have := congrFun (congrFun hm (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [matN] using this

theorem pkMat_ONE : pkMat 6 ONE = 1 := by decide +kernel

theorem matArr_one : matArr 1 = idA () := by
  refine ext64 (size_matArr _) size_idA fun i hi => ?_
  rw [matArr_get _ hi, one_mulVec, codeOf_vecOf i hi, idA_get hi]

theorem arrN_one : arrN ONE = idA () := by
  unfold arrN matN
  rw [pkMat_ONE, Matrix.submatrix_one_equiv, matArr_one]

theorem ONE_lt : ONE < 2 ^ 36 := by decide +kernel

theorem decide_arrN {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) :
    decide (arrN A = arrN B) = Nat.beq A B := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq, Nat.beq_eq]
  exact ⟨arrN_inj hA hB, fun h => by rw [h]⟩

theorem countP_range_congr {n : ℕ} {p q : ℕ → Bool} (h : ∀ i < n, p i = q i) :
    (List.range n).countP p = (List.range n).countP q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_append, ih fun i hi => h i (by omega)]
    simp [h n (by omega)]

variable {R : ℕ → ℕ}

theorem genA_eq (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val)) {j : ℕ}
    (hj : j < 9) : (genA ())[j]! = arrN (R j) := by
  rw [genA, getElem!_ofFn_nat _ (by omega : j < 12)]
  have := hG ⟨j, hj⟩
  unfold arrN matN
  rw [← this]
  rfl

theorem size_gS0 : (gS0 ()).size = 9 := by
  simp [gS0]

theorem gS0_eq (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val)) {j : ℕ}
    (hj : j < 9) : (gS0 ())[j]! = arrN (R j) := by
  simp only [gS0]
  rw [getElem!_ofFn_nat _ hj]
  exact genA_eq hG hj

theorem recX_lt {n : ℕ} (h0 : recX R 9 0 = ONE)
    (hB : ∀ i < n - 1, recF R 9 0 i ≤ i ∧ recF R 9 1 i < 9 ∧
      recX R 9 (i + 1) = rstY R (recX R 9 (recF R 9 0 i)) (recF R 9 1 i)) :
    ∀ t < n, recX R 9 t < 2 ^ 36 := by
  intro t ht
  cases t with
  | zero => rw [h0]; exact ONE_lt
  | succ t =>
    rw [(hB t (by omega)).2.2]
    exact CFSG.KC.Sp62.MULF_lt _ _

theorem enumS0_inv (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val))
    (h : s0TabK R 512 = true) :
    BInvE (fun t => arrN (recX R 9 t)) (recF R 9 0) (recF R 9 1) 512 (bfsEnum (gS0 ()) 512) ∧
      enumOK (bfsEnum (gS0 ()) 512) (gS0 ()) = true ∧ ∀ t < 512, recX R 9 t < 2 ^ 36 := by
  unfold s0TabK tableKk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  have hBi := CFSG.KC.BfsK.buildG_at hB (by norm_num)
  obtain ⟨hC0, hCn, hSi⟩ := CFSG.KC.BfsK.stepG_facts hS (by norm_num)
  have hX := CFSG.KC.G2Three.sort_inj hT (by norm_num)
  have hlt := recX_lt h0 hBi
  have hk : 0 < (gS0 ()).size := by rw [size_gS0]; norm_num
  have hd : ∀ t < 512, ∀ t' < 512, arrN (recX R 9 t) = arrN (recX R 9 t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrN_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrN (recX R 9 0) = idA () := by rw [h0, arrN_one]
  have hS' : ∀ i < 512 * (gS0 ()).size, StepE (gS0 ()) (fun t => arrN (recX R 9 t))
      (recF R 9 0) (recF R 9 1) (recC R 9 9) (recPOS R 9 9) 512 i := by
    intro i hi
    rw [size_gS0] at hi
    unfold StepE
    rw [size_gS0]
    obtain ⟨a, b, c, d, e, f⟩ := hSi i hi
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, rstY, ← arrN_mul, gS0_eq hG (Nat.mod_lt _ (by norm_num))]
  have hB' : ∀ i < 512 - 1, recF R 9 0 i ≤ i ∧ recF R 9 1 i < (gS0 ()).size ∧
      arrN (recX R 9 (i + 1)) = compA (arrN (recX R 9 (recF R 9 0 i))) (gS0 ())[recF R 9 1 i]! := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [size_gS0]; exact b, ?_⟩
    rw [c, rstY, ← arrN_mul, gS0_eq hG b]
  have hCn' : recC R 9 9 (512 * (gS0 ()).size) = 512 := by rw [size_gS0]; exact hCn
  have r1 := bfsEnum_replay (fuel := 512) (T := fun t => arrN (recX R 9 t)) (PA := recF R 9 0)
    (PB := recF R 9 1) (C := recC R 9 9) (POS := recPOS R 9 9) (n := 512) hk (by norm_num) le_rfl
    hT0 hd hC0 hCn' hS'
  have r2 := enumOK_of_replay (fuel := 512) (T := fun t => arrN (recX R 9 t)) (PA := recF R 9 0)
    (PB := recF R 9 1) (C := recC R 9 9) (POS := recPOS R 9 9) (n := 512) hk (by norm_num) le_rfl
    hT0 hd hC0 hCn' hS' hB'
  exact ⟨r1, r2, hlt⟩

theorem sqCount_of (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val))
    (h : s0TabK R 512 = true) {A m : ℕ} (hA : A < 2 ^ 36) (hq : s0SqK R A m = true) :
    sqCount (enumS0 ()) (arrN A) = m := by
  obtain ⟨⟨e1, -, -, e4, -⟩, -, hlt⟩ := enumS0_inv hG h
  unfold s0SqK at hq
  rw [Nat.beq_eq] at hq
  unfold enumS0 sqCount countLt
  rw [e1, ← hq]
  refine countP_range_congr fun i hi => ?_
  rw [e4 i hi, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) hA]

theorem commOK_of (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val))
    {A : ℕ} (hc : s0CommK R A = true) : commOK (gS0 ()) (arrN A) = true := by
  have hall := CFSG.KC.G2Three.allBelow_g2 hc (by norm_num)
  unfold commOK
  rw [allLt_iff]
  intro j hj
  rw [size_gS0] at hj
  have e := hall j hj
  unfold commY at e
  rw [Nat.beq_eq] at e
  rw [decide_eq_true_eq, gS0_eq hG hj, arrN_mul, arrN_mul, e]

theorem centerOK_of (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val))
    (h : s0TabK R 512 = true) {A B : ℕ} (hc : s0CentK R A B = true) :
    centerOK (enumS0 ()) (gS0 ()) (arrN A) (arrN B) = true := by
  obtain ⟨⟨e1, -, -, e4, -⟩, -, hlt⟩ := enumS0_inv hG h
  have hall := CFSG.KC.G2Three.allBelow_g2 hc (by norm_num)
  unfold enumS0 centerOK
  dsimp only
  rw [allLt_iff]
  intro i hi
  rw [e1] at hi
  rw [e4 i hi]
  have e := hall i hi
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases e with (((⟨hw, hnc⟩ | e) | e) | e) | e
  · left
    rw [Bool.not_eq_true']
    cases hcm : commOK (gS0 ()) (arrN (recX R 9 i))
    · rfl
    · exfalso
      unfold commOK at hcm
      rw [allLt_iff] at hcm
      have := hcm _ (by rw [size_gS0]; exact hw)
      rw [decide_eq_true_eq, gS0_eq hG hw, arrN_mul, arrN_mul] at this
      have e' := arrN_inj (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _) this
      unfold commY at hnc
      rw [Bool.not_eq_true', e'] at hnc
      exact absurd (Nat.beq_refl _) (by rw [hnc]; decide)
  · exact Or.inr (Or.inl (by rw [e, arrN_one]))
  · exact Or.inr (Or.inr (Or.inl (by rw [e])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [e, arrN_mul]))))

theorem cert550801_of (hG : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R j.val))
    (hGb : ∀ j < 9, R j < 2 ^ 36) (h : s0TabK R 512 = true) (h1 : s0SqK R ONE 144 = true)
    (ha : s0SqK R (R 5) 0 = true) (hb : s0SqK R (R 4) 48 = true)
    (hab : s0SqK R (MULF (R 5) (R 4)) 32 = true) (hca : s0CommK R (R 5) = true)
    (hcb : s0CommK R (R 4) = true) (hz : s0CentK R (R 5) (R 4) = true) :
    (enumOK (enumS0 ()) (gS0 ()) = true)
    ∧ (sqCount (enumS0 ()) (idA ()) = 144)
    ∧ (sqCount (enumS0 ()) (genA ())[5]! = 0)
    ∧ (sqCount (enumS0 ()) (genA ())[4]! = 48)
    ∧ (sqCount (enumS0 ()) (compA (genA ())[5]! (genA ())[4]!) = 32)
    ∧ (commOK (gS0 ()) (genA ())[5]! = true)
    ∧ (commOK (gS0 ()) (genA ())[4]! = true)
    ∧ (centerOK (enumS0 ()) (gS0 ()) (genA ())[5]! (genA ())[4]! = true) := by
  have g5 := genA_eq hG (by norm_num : 5 < 9)
  have g4 := genA_eq hG (by norm_num : 4 < 9)
  rw [g5, g4, arrN_mul, ← arrN_one]
  have he : enumOK (enumS0 ()) (gS0 ()) = true := by
    unfold enumS0
    exact (enumS0_inv hG h).2.1
  exact ⟨he, sqCount_of hG h ONE_lt h1, sqCount_of hG h (hGb 5 (by norm_num)) ha,
    sqCount_of hG h (hGb 4 (by norm_num)) hb, sqCount_of hG h (CFSG.KC.Sp62.MULF_lt _ _) hab,
    commOK_of hG hca, commOK_of hG hcb, centerOK_of hG h hz⟩

end CFSG.KC.YamakiS0

end
