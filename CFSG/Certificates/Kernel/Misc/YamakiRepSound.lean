module

public import Certificates.Data.Kernel.Misc.YamakiRep
public import Certificates.Data.Sp62RecCR1CE
public import CFSG.Certificates.Kernel.Misc.YamakiA0Sound
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.YamakiRep

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiRep
  CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiA0
  CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n k : ℕ}

theorem rows_of_chunks {L m : ℕ} (h : ∀ q < m, chunkK R st o n k L q = true) (hm : n ≤ L * m) :
    ∀ t < n, rowK R st o n k t = true := by
  intro t ht
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hm; omega
  have hq : t / L < m := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; omega)
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 (h _ hq) t (Nat.mul_div_le t L) (by
    have := Nat.lt_div_mul_add (a := t) hL
    rw [Nat.mul_comm] at this
    exact this)
  have hb : Nat.blt t n = true := Nat.blt_eq.mpr ht
  rw [hb, cond_true] at e
  exact e

theorem build_of_rows (h : ∀ t < n, rowK R st o n k t = true) :
    ∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < k ∧
      recX R o (i + 1) = st (recX R o (recF R o 0 i)) (recF R o 1 i) := by
  intro i hi
  have e := h i (by omega)
  unfold rowK buildAt at e
  have hb : Nat.blt (Nat.succ i) n = true := Nat.blt_eq.mpr (by omega)
  rw [hb, cond_true] at e
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at e
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, -⟩, -⟩ := e
  exact ⟨a, b, c⟩

theorem stepAt_facts {X PA PB C POS : ℕ → ℕ} {i : ℕ}
    (h : stepAt st X PA PB C POS n k i = true) :
    i / k < C i ∧ POS i ≤ C i ∧ POS i < n ∧ X (POS i) = st (X (i / k)) (i % k) ∧
      (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / k ∧ PB (C i - 1) = i % k) ∧
      (POS i ≠ C i → C (i + 1) = C i) := by
  unfold stepAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  refine ⟨a, b, c, d, fun hpc => ?_, fun hpc => ?_⟩
  · have hb : Nat.beq (POS i) (C i) = true := Nat.beq_eq.mpr hpc
    rw [hb, cond_true] at e
    simp only [Bool.and_eq_true, Nat.beq_eq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    rw [Nat.pred_eq_sub_one] at e2 e3
    exact ⟨e1, e2, e3⟩
  · have hb : Nat.beq (POS i) (C i) = false := by
      cases hq : Nat.beq (POS i) (C i)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hq) hpc
    rw [hb, cond_false] at e
    exact Nat.eq_of_beq_eq_true e

theorem step_of_rows (hk0 : 0 < k) (hk : k ≤ 64) (h : ∀ t < n, rowK R st o n k t = true) :
    ∀ i < n * k, stepAt st (recX R o) (recF R o 0) (recF R o 1) (recC R o k) (recPOS R o k) n k i =
      true := by
  intro i hi
  have ht : i / k < n := (Nat.div_lt_iff_lt_mul hk0).2 hi
  have e := h (i / k) ht
  unfold rowK at e
  simp only [Bool.and_eq_true] at e
  have e2 := CFSG.KC.G2Three.allBelow_g2 e.1.2 (by omega) (i % k) (Nat.mod_lt _ hk0)
  have hi' : Nat.add (Nat.mul (i / k) k) (i % k) = i := Nat.div_add_mod' i k
  rw [hi'] at e2
  exact e2

theorem sort_of_rows (h : ∀ t < n, rowK R st o n k t = true) :
    ∀ t < n, ∀ t' < n, recX R o t = recX R o t' → t = t' := by
  refine CFSG.KC.G2Three.inj_of_sorted (SRT := recF R o 2) (SRI := recF R o 3) (fun i hi => ?_)
    (fun i hi1 => ?_)
  · have e := h i hi
    unfold rowK sortAt at e
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    obtain ⟨-, ⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩ := e
    exact ⟨a, b, c, d⟩
  · have e := h i (by omega)
    unfold rowK sortAt at e
    simp only [Bool.and_eq_true] at e
    have e2 := e.2.2
    have hb : Nat.blt (Nat.succ i) n = true := Nat.blt_eq.mpr hi1
    rw [hb, cond_true] at e2
    exact Nat.blt_eq.mp e2

theorem recX_lt {g : ℕ} (h0 : recX R o 0 = ONE)
    (hB : ∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < k ∧
      recX R o (i + 1) = rstG R g (recX R o (recF R o 0 i)) (recF R o 1 i)) :
    ∀ t < n, recX R o t < 2 ^ 36 := by
  intro t ht
  cases t with
  | zero => rw [h0]; exact ONE_lt
  | succ t =>
    rw [(hB t (by omega)).2.2]
    exact CFSG.KC.Sp62.MULF_lt _ _

theorem table_inv {gs : Array (Array ℕ)} {g : ℕ} (hk : gs.size = k) (hk0 : 0 < k) (hk64 : k ≤ 64)
    (hn : 0 < n) (hg : ∀ j < k, gs[j]! = arrN (R (g + j))) (hh : headK R o n k = true)
    (hr : ∀ t < n, rowK R (rstG R g) o n k t = true) :
    BInvE (fun t => arrN (recX R o t)) (recF R o 0) (recF R o 1) n (bfsEnum gs n) ∧
      enumOK (bfsEnum gs n) gs = true ∧ recX R o 0 = ONE ∧
      (∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < k ∧
        recX R o (i + 1) = MULF (recX R o (recF R o 0 i)) (R (g + recF R o 1 i))) ∧
      ∀ t < n, recX R o t < 2 ^ 36 := by
  unfold headK at hh
  simp only [Bool.and_eq_true, Nat.beq_eq] at hh
  obtain ⟨⟨h0, hC0⟩, hCn⟩ := hh
  have hBi := build_of_rows hr
  have hSi := step_of_rows hk0 hk64 hr
  have hX := sort_of_rows hr
  have hlt := recX_lt h0 hBi
  have hk' : 0 < gs.size := by rw [hk]; exact hk0
  have hd : ∀ t < n, ∀ t' < n, arrN (recX R o t) = arrN (recX R o t') → t = t' :=
    fun t ht t' ht' e => hX t ht t' ht' (arrN_inj (hlt t ht) (hlt t' ht') e)
  have hT0 : arrN (recX R o 0) = idA () := by rw [h0, arrN_one]
  have hS' : ∀ i < n * gs.size, StepE gs (fun t => arrN (recX R o t))
      (recF R o 0) (recF R o 1) (recC R o k) (recPOS R o k) n i := by
    intro i hi
    rw [hk] at hi
    unfold StepE
    rw [hk]
    obtain ⟨a, b, c, d, e, f⟩ := stepAt_facts (hSi i hi)
    refine ⟨a, b, c, ?_, e, f⟩
    beta_reduce
    rw [d, rstG, Nat.add_eq, ← arrN_mul, hg _ (Nat.mod_lt _ hk0)]
  have hB' : ∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < gs.size ∧
      arrN (recX R o (i + 1)) = compA (arrN (recX R o (recF R o 0 i))) gs[recF R o 1 i]! := by
    intro i hi
    obtain ⟨a, b, c⟩ := hBi i hi
    refine ⟨a, by rw [hk]; exact b, ?_⟩
    rw [c, rstG, Nat.add_eq, ← arrN_mul, hg _ b]
  have hCn' : recC R o k (n * gs.size) = n := by rw [hk]; exact hCn
  have r1 := bfsEnum_replay (fuel := n) (T := fun t => arrN (recX R o t)) (PA := recF R o 0)
    (PB := recF R o 1) (C := recC R o k) (POS := recPOS R o k) (n := n) hk' hn le_rfl hT0 hd hC0
    hCn' hS'
  have r2 := enumOK_of_replay (fuel := n) (T := fun t => arrN (recX R o t))
    (PA := recF R o 0) (PB := recF R o 1) (C := recC R o k) (POS := recPOS R o k) (n := n)
    hk' hn le_rfl hT0 hd hC0 hCn' hS' hB'
  refine ⟨r1, r2, h0, fun i hi => ?_, hlt⟩
  obtain ⟨a, b, c⟩ := hBi i hi
  exact ⟨a, b, by rw [c, rstG, Nat.add_eq]⟩

theorem words_gen (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) :
    ∀ (ws : List (List ℕ)) (g : ℕ), (∀ w ∈ ws, ∀ i ∈ w, i < 12) → genWK R g ws = true →
      ∀ j < ws.length, wordA (genA ()) (ws.getD j []) = arrN (R (g + j))
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | w :: ws, g, hw, h, j, hj => by
    unfold genWK at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero =>
      rw [List.getD_cons_zero, wordA_eq hG w (hw w List.mem_cons_self), Nat.add_zero, h.1]
    | succ j =>
      rw [List.getD_cons_succ, words_gen hG ws (Nat.succ g)
        (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h.2 j (by simpa using hj)]
      have e : Nat.succ g + j = g + (j + 1) := by omega
      rw [e]

theorem wordsA_get (gs : Array (Array ℕ)) (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    (wordsA gs ws)[j]! = wordA gs (ws.getD j []) := by
  unfold wordsA
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem words_inv (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {ws : List (List ℕ)}
    {L m : ℕ} (hws : ∀ w ∈ ws, ∀ i ∈ w, i < 12) (hk : ws.length = k) (hk0 : 0 < k)
    (hk64 : k ≤ 64) (hn : 0 < n) (hm : n ≤ L * m) (hw : genWK R 12 ws = true)
    (hh : headK R o n k = true) (hc : ∀ q < m, chunkK R (rstG R 12) o n k L q = true) :
    BInvE (fun t => arrN (recX R o t)) (recF R o 0) (recF R o 1) n
        (bfsEnum (wordsA (genA ()) ws) n) ∧
      enumOK (bfsEnum (wordsA (genA ()) ws) n) (wordsA (genA ()) ws) = true ∧ recX R o 0 = ONE ∧
      (∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < k ∧
        recX R o (i + 1) = MULF (recX R o (recF R o 0 i)) (R (12 + recF R o 1 i))) ∧
      ∀ t < n, recX R o t < 2 ^ 36 := by
  refine table_inv (by unfold wordsA; simpa using hk) hk0 hk64 hn (fun j hj => ?_) hh
    (rows_of_chunks hc hm)
  rw [wordsA_get _ _ (by omega), words_gen hG ws 12 hws hw j (by omega)]

theorem idx_gen : ∀ (is : List ℕ) (g : ℕ), genIK R g is = true →
    ∀ j < is.length, R (g + j) = R (is.getD j 0)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i :: is, g, h, j, hj => by
    unfold genIK at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => rw [List.getD_cons_zero, Nat.add_zero, h.1]
    | succ j =>
      rw [List.getD_cons_succ, ← idx_gen is (Nat.succ g) h.2 j (by simpa using hj)]
      have e : Nat.succ g + j = g + (j + 1) := by omega
      rw [e]

theorem v0_inv (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hw : genIK R 12 v0Idx = true)
    (hh : headK R o 32 5 = true) (hc : chunkK R (rstG R 12) o 32 5 32 0 = true) :
    BInvE (fun t => arrN (recX R o t)) (recF R o 0) (recF R o 1) 32 (enumV0 ()) ∧
      enumOK (enumV0 ()) (gV0 ()) = true ∧ recX R o 0 = ONE ∧
      (∀ i < 32 - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < 5 ∧
        recX R o (i + 1) = MULF (recX R o (recF R o 0 i)) (R (12 + recF R o 1 i))) ∧
      ∀ t < 32, recX R o t < 2 ^ 36 := by
  refine table_inv (by simp [gV0]) (by norm_num) (by norm_num) (by norm_num) (fun j hj => ?_) hh
    (rows_of_chunks (m := 1) (fun q hq => by rw [Nat.lt_one_iff.1 hq]; exact hc) le_rfl)
  have hi : v0Idx.getD j 0 < 12 := by
    have : ∀ j < 5, v0Idx.getD j 0 < 12 := by decide
    exact this j hj
  simp only [gV0]
  rw [getElem!_ofFn_nat _ hj, genA_eq12 hG hi, idx_gen v0Idx 12 hw j (lt_of_lt_of_eq hj rfl)]

end CFSG.KC.YamakiRep

end
