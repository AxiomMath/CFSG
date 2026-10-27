module

public import Certificates.Data.Kernel.Misc.YamakiA0
public import CFSG.Certificates.Kernel.Misc.YamakiS0Sound

public section

namespace CFSG.KC.YamakiA0

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiA0
  CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.Misc.Spec Matrix
open CFSG.KD.Sp62 (MULF ONE)

theorem abel_of_tree {α : Type*} [Monoid α] {M G : ℕ → α} {PA PB : ℕ → ℕ} {n k : ℕ}
    (h0 : M 0 = 1)
    (hB : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ M (i + 1) = M (PA i) * G (PB i))
    (hsq : ∀ j < k, G j * G j = 1) (hc : ∀ j < k, ∀ j' < k, G j * G j' = G j' * G j) :
    (∀ t < n, M t * M t = 1) ∧ ∀ t < n, ∀ t' < n, M t * M t' = M t' * M t := by
  have c1 : ∀ t < n, ∀ j < k, M t * G j = G j * M t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht j hj
      cases t with
      | zero => rw [h0, one_mul, mul_one]
      | succ i =>
        obtain ⟨p1, p2, p3⟩ := hB i (by omega)
        rw [p3, mul_assoc, hc _ p2 _ hj, ← mul_assoc, ih _ (by omega) (by omega) j hj, mul_assoc]
  refine ⟨fun t => ?_, fun t ht t' => ?_⟩
  · induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      cases t with
      | zero => rw [h0, one_mul]
      | succ i =>
        obtain ⟨p1, p2, p3⟩ := hB i (by omega)
        rw [p3, mul_assoc, ← mul_assoc (G (PB i)), ← c1 _ (by omega) _ p2, mul_assoc,
          ← mul_assoc (M (PA i)), ih _ (by omega) (by omega), hsq _ p2, one_mul]
  · induction t' using Nat.strong_induction_on with
    | _ t' ih =>
      intro ht'
      cases t' with
      | zero => rw [h0, one_mul, mul_one]
      | succ i =>
        obtain ⟨p1, p2, p3⟩ := hB i (by omega)
        rw [p3, ← mul_assoc, ih _ (by omega) (by omega), mul_assoc, c1 t ht _ p2, ← mul_assoc]

variable {R : ℕ → ℕ}

theorem genA_eq12 (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {j : ℕ} (hj : j < 12) :
    (genA ())[j]! = arrN (R j) := by
  rw [genA, getElem!_ofFn_nat _ hj]
  have := hG ⟨j, hj⟩
  unfold arrN matN
  rw [← this]
  rfl

theorem size_gA0 : (gA0 ()).size = 6 := by
  simp [gA0]

theorem gA0_eq (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {j : ℕ} (hj : j < 6) :
    (gA0 ())[j]! = arrN (R (j + 3)) := by
  simp only [gA0]
  rw [getElem!_ofFn_nat _ hj]
  exact genA_eq12 hG (by omega)

theorem matN_ONE : matN ONE = 1 := by
  unfold matN
  rw [pkMat_ONE, Matrix.submatrix_one_equiv]

theorem wordN_lt (w : List ℕ) : wordN R w < 2 ^ 36 := by
  cases w with
  | nil => exact ONE_lt
  | cons i w => exact CFSG.KC.Sp62.MULF_lt _ _

theorem wordA_eq (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) :
    ∀ w : List ℕ, (∀ i ∈ w, i < 12) → wordA (genA ()) w = arrN (wordN R w)
  | [], _ => by rw [wordA, wordN, arrN_one]
  | i :: w, h => by
    rw [wordA, wordN, genA_eq12 hG (h i List.mem_cons_self),
      wordA_eq hG w fun j hj => h j (List.mem_cons_of_mem _ hj), arrN_mul]

theorem recX_lt12 {n : ℕ} (h0 : recX R 12 0 = ONE)
    (hB : ∀ i < n - 1, recF R 12 0 i ≤ i ∧ recF R 12 1 i < 6 ∧
      recX R 12 (i + 1) = rstA R (recX R 12 (recF R 12 0 i)) (recF R 12 1 i)) :
    ∀ t < n, recX R 12 t < 2 ^ 36 := by
  intro t ht
  cases t with
  | zero => rw [h0]; exact ONE_lt
  | succ t =>
    rw [(hB t (by omega)).2.2]
    exact CFSG.KC.Sp62.MULF_lt _ _

theorem enumA0_inv (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (h : a0TabK R 64 = true) :
    BInvE (fun t => arrN (recX R 12 t)) (recF R 12 0) (recF R 12 1) 64 (bfsEnum (gA0 ()) 64) ∧
      enumOK (bfsEnum (gA0 ()) 64) (gA0 ()) = true ∧ recX R 12 0 = ONE ∧
      (∀ i < 64 - 1, recF R 12 0 i ≤ i ∧ recF R 12 1 i < 6 ∧
        recX R 12 (i + 1) = rstA R (recX R 12 (recF R 12 0 i)) (recF R 12 1 i)) ∧
      ∀ t < 64, recX R 12 t < 2 ^ 36 := by
  unfold a0TabK tableKk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  have hBi := CFSG.KC.BfsK.buildG_at hB (by norm_num)
  obtain ⟨hC0, hCn, hSi⟩ := CFSG.KC.BfsK.stepG_facts hS (by norm_num)
  have hX := CFSG.KC.G2Three.sort_inj hT (by norm_num)
  have hlt := recX_lt12 h0 hBi
  have hk : 0 < (gA0 ()).size := by rw [size_gA0]; norm_num
  have hd : ∀ t < 64, ∀ t' < 64, arrN (recX R 12 t) = arrN (recX R 12 t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrN_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrN (recX R 12 0) = idA () := by rw [h0, arrN_one]
  have hS' : ∀ i < 64 * (gA0 ()).size, StepE (gA0 ()) (fun t => arrN (recX R 12 t))
      (recF R 12 0) (recF R 12 1) (recC R 12 6) (recPOS R 12 6) 64 i := by
    intro i hi
    rw [size_gA0] at hi
    unfold StepE
    rw [size_gA0]
    obtain ⟨a, b, c, d, e, f⟩ := hSi i hi
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, rstA, Nat.add_eq, ← arrN_mul, gA0_eq hG (Nat.mod_lt _ (by norm_num))]
  have hB' : ∀ i < 64 - 1, recF R 12 0 i ≤ i ∧ recF R 12 1 i < (gA0 ()).size ∧
      arrN (recX R 12 (i + 1)) =
        compA (arrN (recX R 12 (recF R 12 0 i))) (gA0 ())[recF R 12 1 i]! := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [size_gA0]; exact b, ?_⟩
    rw [c, rstA, Nat.add_eq, ← arrN_mul, gA0_eq hG b]
  have hCn' : recC R 12 6 (64 * (gA0 ()).size) = 64 := by rw [size_gA0]; exact hCn
  have r1 := bfsEnum_replay (fuel := 64) (T := fun t => arrN (recX R 12 t)) (PA := recF R 12 0)
    (PB := recF R 12 1) (C := recC R 12 6) (POS := recPOS R 12 6) (n := 64) hk (by norm_num)
    le_rfl hT0 hd hC0 hCn' hS'
  have r2 := enumOK_of_replay (fuel := 64) (T := fun t => arrN (recX R 12 t))
    (PA := recF R 12 0) (PB := recF R 12 1) (C := recC R 12 6) (POS := recPOS R 12 6) (n := 64)
    hk (by norm_num) le_rfl hT0 hd hC0 hCn' hS' hB'
  exact ⟨r1, r2, h0, hBi, hlt⟩

theorem a0AbelCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (h : a0TabK R 64 = true) (hg : a0GenK R = true) : a0AbelCheck () = true := by
  obtain ⟨⟨e1, -, -, e4, -⟩, -, h0, hB, -⟩ := enumA0_inv hG h
  have hgen := CFSG.KC.G2Three.allBelow_g2 hg (by norm_num)
  have hsq : ∀ j < 6, matN (R (j + 3)) * matN (R (j + 3)) = 1 := by
    intro j hj
    have e := hgen j hj
    simp only [Bool.and_eq_true, Nat.beq_eq] at e
    have e1 : MULF (R (j + 3)) (R (j + 3)) = ONE := e.1
    rw [← matN_mul, e1, matN_ONE]
  have hc : ∀ j < 6, ∀ j' < 6,
      matN (R (j + 3)) * matN (R (j' + 3)) = matN (R (j' + 3)) * matN (R (j + 3)) := by
    intro j hj j' hj'
    have e := hgen j hj
    simp only [Bool.and_eq_true, Nat.beq_eq] at e
    have e2 := CFSG.KC.G2Three.allBelow_g2 e.2 (by norm_num) j' hj'
    unfold commA at e2
    rw [Nat.beq_eq, Nat.add_eq, Nat.add_eq] at e2
    rw [← matN_mul, ← matN_mul, e2]
  have hB' : ∀ i < 64 - 1, recF R 12 0 i ≤ i ∧ recF R 12 1 i < 6 ∧
      matN (recX R 12 (i + 1)) =
        matN (recX R 12 (recF R 12 0 i)) * matN (R (recF R 12 1 i + 3)) := by
    intro i hi
    obtain ⟨a, b, c⟩ := hB i hi
    exact ⟨a, b, by rw [c, rstA, Nat.add_eq, matN_mul]⟩
  have hM0 : matN (recX R 12 0) = 1 := by rw [h0, matN_ONE]
  obtain ⟨sq, cm⟩ := abel_of_tree (M := fun t => matN (recX R 12 t))
    (G := fun j => matN (R (j + 3))) hM0 hB' hsq hc
  unfold a0AbelCheck enumA0
  simp only [allLt_iff, Bool.and_eq_true, decide_eq_true_eq]
  intro i hi
  rw [e1] at hi
  refine ⟨?_, fun j hj => ?_⟩
  · rw [e4 i hi]
    unfold arrN
    rw [compA_matArr, ← matArr_one, sq i hi]
  · rw [e1] at hj
    rw [e4 i hi, e4 j hj]
    unfold arrN
    rw [compA_matArr, compA_matArr, cm i hi j hj]

theorem a0EnumCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (h : a0TabK R 64 = true) {R' : ℕ → ℕ}
    (hG' : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R' j.val))
    (hS : CFSG.KD.YamakiS0.s0TabK R' 512 = true) : a0EnumCheck () = true := by
  obtain ⟨⟨e1, -⟩, he, -⟩ := enumA0_inv hG h
  have hs := (enumS0_inv hG' hS).1.1
  unfold a0EnumCheck enumA0 enumS0
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨he, e1⟩, hs⟩

theorem hhatAlphaCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hh : hhatK R = true) : hhatAlphaCheck () = true := by
  have hI : ∀ i ∈ idxHhat, i < 12 := by decide
  unfold hhatK at hh
  unfold hhatAlphaCheck
  simp only [List.all_eq_true, decide_eq_true_eq] at hh ⊢
  intro i hi
  have e := hh i hi
  unfold commA at e
  rw [Nat.beq_eq] at e
  rw [genA_eq12 hG (hI i hi), genA_eq12 hG (by norm_num : 5 < 12), arrN_mul, arrN_mul, e]

theorem fourOK_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {x c₁ c₂ : List ℕ}
    (h1 : ∀ i ∈ x, i < 12) (h2 : ∀ i ∈ conjWord c₁ x, i < 12) (h3 : ∀ i ∈ conjWord c₂ x, i < 12)
    (hf : fourK R x c₁ c₂ = true) : fourOK x c₁ c₂ = true := by
  unfold fourK commA at hf
  unfold fourOK
  dsimp only at hf ⊢
  rw [wordA_eq hG x h1, wordA_eq hG _ h2, wordA_eq hG _ h3, ← arrN_one, arrN_mul, arrN_mul,
    decide_arrN (wordN_lt _) ONE_lt, decide_arrN (wordN_lt _) (wordN_lt _),
    decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
    decide_arrN (wordN_lt _) (CFSG.KC.Sp62.MULF_lt _ _)]
  exact hf

theorem fourCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hf : fourCheckK R = true) : fourCheck () = true := by
  unfold fourCheckK at hf
  unfold fourCheck
  rw [Bool.and_eq_true] at hf ⊢
  exact ⟨fourOK_of hG (by decide) (by decide) (by decide) hf.1,
    fourOK_of hG (by decide) (by decide) (by decide) hf.2⟩

theorem cert550821_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (h : a0TabK R 64 = true) (hg : a0GenK R = true) (hh : hhatK R = true)
    (hf : fourCheckK R = true) {R' : ℕ → ℕ}
    (hG' : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (R' j.val))
    (hS : CFSG.KD.YamakiS0.s0TabK R' 512 = true) :
    (a0EnumCheck () = true) ∧ (a0AbelCheck () = true) ∧ (hhatAlphaCheck () = true) ∧
      (fourCheck () = true) :=
  ⟨a0EnumCheck_of hG h hG' hS, a0AbelCheck_of hG h hg, hhatAlphaCheck_of hG hh,
    fourCheck_of hG hf⟩

end CFSG.KC.YamakiA0

end
