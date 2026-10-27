module

public import Certificates.Data.Kernel.Misc.OmegaSixO
public import CFSG.Certificates.Kernel.Misc.OmegaSixClassSound

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.YamakiGenPos CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.ConjEnum
  CFSG.KC.YamakiRep CFSG.KC.YamakiRepF CFSG.KC.YamakiGenPos CFSG.KC.Loop CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

section Three

variable {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n : ℕ}

theorem allBelow_three {f : ℕ → Bool} (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true) :
    allBelow 3 1 f = true := by
  unfold allBelow
  refine (recAndY_iff _ 1).2 fun h' _ => (recAndY_iff (fun l => (fun i =>
    bIf(Nat.blt i 3, f i, true)) (Nat.add (Nat.shiftLeft h' 6) l)) 64).2 fun l _ => ?_
  dsimp only
  by_cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) 3 = true
  · rw [hb]
    have hi := Nat.blt_eq.mp hb
    rcases (by omega : Nat.add (Nat.shiftLeft h' 6) l = 0 ∨ Nat.add (Nat.shiftLeft h' 6) l = 1 ∨
      Nat.add (Nat.shiftLeft h' 6) l = 2) with e | e | e
    · rw [e]
      exact h0
    · rw [e]
      exact h1
    · rw [e]
      exact h2
  · rw [Bool.eq_false_iff.2 hb]

theorem stepAt_of_stepF3 {t s i : ℕ} (hd : Nat.div i 3 = t) (hm : Nat.mod i 3 = s)
    (h : stepF R st o n t s (recX R o t) (recC R o 3 i) (recPOS R o 3 i)
      (recC R o 3 (Nat.succ i)) = true) :
    stepAt st (recX R o) (recF R o 0) (recF R o 1) (recC R o 3) (recPOS R o 3) n 3 i = true := by
  unfold stepAt
  rw [hd, hm]
  exact h

theorem recF_at3 {i t s : ℕ} (hd : Nat.div i 3 = t) (hm : Nat.mod i 3 = s) :
    recC R o 3 i = fld (R (Nat.add o t)) (Nat.add 4 s) ∧
      recPOS R o 3 i = fld (R (Nat.add o t)) (Nat.add 7 s) := by
  refine ⟨?_, ?_⟩
  · unfold recC
    rw [hd, hm]
    rfl
  · unfold recPOS
    rw [hd, hm]
    rfl

theorem rowK_of_rowF3 {t : ℕ} (h : rowF3 R st o n t = true) : rowK R st o n 3 t = true := by
  unfold rowF3 rowB3 at h
  simp only [strictY_eq] at h
  obtain ⟨⟨⟨⟨hb, h0⟩, h1⟩, h2⟩, hs⟩ := (Bool.and_eq_true_iff.1 h).imp_left fun h =>
    (Bool.and_eq_true_iff.1 h).imp_left fun h => (Bool.and_eq_true_iff.1 h).imp_left fun h =>
      Bool.and_eq_true_iff.1 h
  have e : ∀ s, s < 3 → Nat.div (Nat.add (Nat.mul t 3) s) 3 = t ∧
      Nat.mod (Nat.add (Nat.mul t 3) s) 3 = s := by
    intro s hs
    change (t * 3 + s) / 3 = t ∧ (t * 3 + s) % 3 = s
    omega
  have e' : ∀ s, s < 2 → Nat.div (Nat.succ (Nat.add (Nat.mul t 3) s)) 3 = t ∧
      Nat.mod (Nat.succ (Nat.add (Nat.mul t 3) s)) 3 = s + 1 := by
    intro s hs
    change (t * 3 + s + 1) / 3 = t ∧ (t * 3 + s + 1) % 3 = s + 1
    omega
  have e2 : Nat.div (Nat.succ (Nat.add (Nat.mul t 3) 2)) 3 = Nat.succ t ∧
      Nat.mod (Nat.succ (Nat.add (Nat.mul t 3) 2)) 3 = 0 := by
    change (t * 3 + 2 + 1) / 3 = t + 1 ∧ (t * 3 + 2 + 1) % 3 = 0
    omega
  unfold rowK
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  refine ⟨⟨hb, allBelow_three ?_ ?_ ?_⟩, hs⟩
  · obtain ⟨d, m⟩ := e 0 (by omega)
    obtain ⟨d', m'⟩ := e' 0 (by omega)
    refine stepAt_of_stepF3 d m ?_
    rw [(recF_at3 d m).1, (recF_at3 d m).2, (recF_at3 d' m').1]
    exact h0
  · obtain ⟨d, m⟩ := e 1 (by omega)
    obtain ⟨d', m'⟩ := e' 1 (by omega)
    refine stepAt_of_stepF3 d m ?_
    rw [(recF_at3 d m).1, (recF_at3 d m).2, (recF_at3 d' m').1]
    exact h1
  · obtain ⟨d, m⟩ := e 2 (by omega)
    refine stepAt_of_stepF3 d m ?_
    rw [(recF_at3 d m).1, (recF_at3 d m).2, (recF_at3 e2.1 e2.2).1]
    exact h2

theorem chunkK_of_chunkF3 {L q : ℕ} (h : chunkF3 R st o n L q = true) :
    chunkK R st o n 3 L q = true := by
  unfold chunkF3 at h
  unfold chunkK
  rw [CFSG.KC.Misc.Clos.allR_iff] at h ⊢
  intro t h1 h2
  have e := h t h1 h2
  cases hb : Nat.blt t n
  · rfl
  · rw [hb, cond_true] at e
    rw [cond_true]
    exact rowK_of_rowF3 e

end Three

theorem anyK_sound (f : ℕ → Bool) : ∀ k, anyK k f = true → ∃ i < k, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | k + 1, h => by
    change bIf(f k, true, anyK k f) = true at h
    cases e : f k
    · rw [e] at h
      obtain ⟨i, hi, hf⟩ := anyK_sound f k h
      exact ⟨i, by omega, hf⟩
    · exact ⟨k, by omega, e⟩

theorem bitK_eq (X p : ℕ) : bitK X p = (if X.testBit p then 1 else 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (X >>> p) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ p) with h | h <;> simp [h]

theorem mulVec_pow (X c : ℕ) (hc : c < 6) (a : Fin 2 ⊕ Fin 2 ⊕ Fin 2) :
    (matF X *ᵥ cvec (2 ^ c)) a = if X.testBit (6 * (bit6 a).val + c) then 1 else 0 := by
  interval_cases c <;> rcases a with i | i | i <;> fin_cases i <;>
    simp (config := { decide := true }) [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, cvec, bit6, matF, ofBits, pkMat, Nat.testBit_two_pow] <;>
    split_ifs <;> simp_all

theorem mulVec_val (X c : ℕ) (hc : c < 6) (a : Fin 2 ⊕ Fin 2 ⊕ Fin 2) :
    ((matF X *ᵥ cvec (2 ^ c)) a).val = if X.testBit (6 * (bit6 a).val + c) then 1 else 0 := by
  rw [mulVec_pow X c hc a]
  split <;> rfl

theorem mulVec_finVal (X c : ℕ) (hc : c < 6) (a : Fin 2 ⊕ Fin 2 ⊕ Fin 2) :
    Fin.val (n := 2) ((matF X *ᵥ cvec (2 ^ c)) a) =
      if X.testBit (6 * (bit6 a).val + c) then 1 else 0 :=
  mulVec_val X c hc a

theorem arrF_get_col (X c : ℕ) (hc : c < 6) : (arrF X)[2 ^ c]! = colK X c := by
  have h64 : 2 ^ c < 64 := by
    calc 2 ^ c < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hc
      _ = 64 := by norm_num
  rw [arrF, marr_get _ h64, vcode]
  simp only [mulVec_val X c hc, mulVec_finVal X c hc, colK, bitK_eq, Nat.add_eq, Nat.mul_eq]
  simp only [bit6, Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
    Nat.mul_one, Nat.reduceMul, Nat.reduceAdd]
  simp only [Nat.add_assoc]
  rfl

theorem subOne_eq (X c : ℕ) (hc : c < 6) : subOneCode (arrF X) (2 ^ c) = subK X c := by
  rw [subOneCode, arrF_get_col X c hc, subK]
  change _ = colK X c ^^^ (1 <<< c)
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem twoNZ_of {X : ℕ} (h : twoNZK X = true) : twoNZ (arrF X) = true := by
  obtain ⟨c, hc, h1⟩ := anyK_sound _ 6 h
  rw [strictY_eq] at h1
  cases ha : Nat.beq (subK X c) 0
  · rw [ha] at h1
    change anyK 6 _ = true at h1
    obtain ⟨d, hd, h2⟩ := anyK_sound _ 6 h1
    rw [strictY_eq] at h2
    cases hb : Nat.beq (subK X d) 0
    · rw [hb] at h2
      change bIf(Nat.beq (subK X c) (subK X d), false, true) = true at h2
      cases hab : Nat.beq (subK X c) (subK X d)
      · have h64 : ∀ c < 6, 2 ^ c < 64 := fun c hc => by
          calc 2 ^ c < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hc
            _ = 64 := by norm_num
        have ha' : subK X c ≠ 0 := fun e => by rw [e] at ha; exact absurd ha (by decide)
        have hb' : subK X d ≠ 0 := fun e => by rw [e] at hb; exact absurd hb (by decide)
        have hab' : subK X d ≠ subK X c := fun e => by
          rw [e, Nat.beq_refl] at hab
          exact absurd hab (by decide)
        simp only [twoNZ, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨2 ^ c, h64 c hc, by rw [subOne_eq X c hc]; exact ha', 2 ^ d, h64 d hd,
          by rw [subOne_eq X d hd]; exact hb', by rw [subOne_eq X d hd, subOne_eq X c hc]; exact hab'⟩
      · rw [hab] at h2
        exact absurd h2 Bool.false_ne_true
    · rw [hb] at h2
      exact absurd h2 Bool.false_ne_true
  · rw [ha] at h1
    exact absurd h1 Bool.false_ne_true

theorem reflAt_arrF {RR : ℕ → ℕ} {nR X : ℕ} {ER : Enum} (hX : X < 2 ^ 36)
    (hE : BInvE (fun t => arrF (recX RR 5 t)) (recF RR 5 0) (recF RR 5 1) nR ER)
    (hs : ∀ m < nR, recF RR 5 2 m < nR) (h : reflAt RR nR X = true) :
    ((ER.lookup (arrF X)).isSome || arrF X == idA () || twoNZ (arrF X)) = true := by
  unfold reflAt at h
  cases h1 : memK RR 5 nR X
  · rw [h1] at h
    change bIf(Nat.beq X ONE, true, twoNZK X) = true at h
    cases h2 : Nat.beq X ONE
    · rw [h2] at h
      change twoNZK X = true at h
      rw [twoNZ_of h]
      simp
    · rw [← arrF_one, beq_arrF hX CFSG.KC.YamakiS0.ONE_lt, h2]
      simp
  · rw [isSome_of_memK hE hs h1]
    simp

theorem a6cAt_arrF {W₁ W₂ Y X : ℕ} (h₁ : W₁ < 2 ^ 36) (h₂ : W₂ < 2 ^ 36) (hY : Y < 2 ^ 36)
    (hX : X < 2 ^ 36) :
    (!(commB (arrF X) (arrF W₁) && commB (arrF X) (arrF W₂)) || arrF X == idA () ||
      arrF X == arrF Y) = a6cAt W₁ W₂ Y X := by
  rw [commB, commB, arrF_mul, arrF_mul, arrF_mul, arrF_mul,
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
    beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), ← arrF_one,
    beq_arrF hX CFSG.KC.YamakiS0.ONE_lt, beq_arrF hX hY, a6cAt]
  cases Nat.beq (MULF X W₁) (MULF W₁ X) <;> cases Nat.beq (MULF X W₂) (MULF W₂ X) <;>
    cases Nat.beq X ONE <;> cases Nat.beq X Y <;> rfl

theorem commArr_arrF (X Y : ℕ) : commArr (arrF X) (arrF Y) = arrF (commK X Y) := by
  rw [commArr, arrF_mul, arrF_mul, arrF_mul, commK]

@[expose] def reflBody (E ER : Enum) (x : Array ℕ) : Bool :=
  conjTreeOK ER (genA6 ()) (genA6Inv ()) x &&
    E.elems.all fun t => (ER.lookup t).isSome || t == idA () || twoNZ t

theorem reflOrbitCheck_eq : reflOrbitCheck () =
    reflBody (bfsEnum (genO ()) 51840) (conjEnum (genA6 ()) (genA6Inv ()) (marr rMat) 100)
      (marr rMat) := rfl

@[expose] def a6Body (E ED EB : Enum) (gs : Array (Array ℕ)) (r c d₁ d₂ : Array ℕ) : Bool :=
  isCentInv E r c && isCentInv E r d₁ && isCentInv E r d₂ && enumOK ED gs &&
    ED.elems.size == 360 &&
    ED.elems.all fun x => !(compA x x == idA ()) || x == idA () || (EB.lookup x).isSome

theorem a6Check_eq : a6Check () =
    a6Body (bfsEnum (genA6 ()) 25920) (bfsEnum (a6Gens ()) 360)
      (conjEnum (genA6 ()) (genA6Inv ()) (marr rBMat) 400) (a6Gens ()) (marr rMat)
      (marr a6cMat) (marr a6d1Mat) (marr a6d2Mat) := rfl

@[expose] def a6CentBody (E : Enum) (w₁ w₂ r : Array ℕ) : Bool :=
  E.elems.all fun t => !(commB t w₁ && commB t w₂) || t == idA () || t == r

theorem a6CentCheck_eq : a6CentCheck () =
    a6CentBody (bfsEnum (genO ()) 51840) (a6Gens ())[0]! (a6Gens ())[1]! (marr rMat) := rfl

section Checks

variable {R S W : ℕ → ℕ}

theorem oEnum_inv {L m : ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (hm : 51840 ≤ L * m) (hh : headK R 3 51840 3 = true)
    (hc : ∀ q < m, chunkF3 R (rstG R 0) 3 51840 L q = true) :
    BInvE (fun t => arrF (recX R 3 t)) (recF R 3 0) (recF R 3 1) 51840
        (bfsEnum (genO ()) 51840) ∧ ∀ t < 51840, recX R 3 t < 2 ^ 36 := by
  have hg : ∀ j < 3, (genO ())[j]! = arrF (R (0 + j)) := by
    intro j hj
    rcases j with _ | _ | _ | j
    · rw [Nat.add_zero, arrF, ← hA]
      rfl
    · rw [Nat.zero_add, arrF, ← hB]
      rfl
    · rw [Nat.zero_add, arrF, ← hr]
      rfl
    · omega
  have T := table_invF (gs := genO ()) (R := R) (o := 3) (n := 51840) (k := 3) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) hg hh
    (rows_of_chunks (L := L) (m := m) (fun q hq => chunkK_of_chunkF3 (hc q hq)) hm)
  exact ⟨T.1, T.2.2⟩

theorem reflOrbitCheck_of {L m L' m' : ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (hr2 : R 2 < 2 ^ 36) (hS4 : S 4 = R 2) (hm : 51840 ≤ L * m)
    (hh : headK R 3 51840 3 = true) (hc : ∀ q < m, chunkF3 R (rstG R 0) 3 51840 L q = true)
    (hd : hdrC S (R 0) (R 1) (S 4) = true) (hhS : headC S 5 36 = true)
    (hcS : ∀ q < 2, chunkF S (cjG S) 5 36 32 q = true) (hm' : 51840 ≤ L' * m')
    (hcl : ∀ q < m', reflChunk R 3 51840 S 36 L' q = true) :
    reflOrbitCheck () = true := by
  have T := oEnum_inv hA hB hr hm hh hc
  have O := orbitO (S := S) (fuel := 100) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hS4]; exact hr2) hd hhS hcS
  have mr : marr rMat = arrF (S 4) := by rw [hS4, hr]; rfl
  rw [reflOrbitCheck_eq, mr, reflBody, O.2.1, Bool.true_and, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 51840 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks L' m' _ hcl i (by omega)
  change bIf(Nat.blt i 51840, strictY (recX R 3 i) (reflAt S 36), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  exact reflAt_arrF (T.2 i hi') O.1 O.2.2.2 hall

theorem a6Check_of {p₅ p₆ p₇ : ℕ} (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hr : rMat = matF (R 2)) (hc : a6cMat = matF (R 5)) (hd₁ : a6d1Mat = matF (R 6))
    (hd₂ : a6d2Mat = matF (R 7)) (hrB : rBMat = matF (S 4)) (hlt : ∀ j < 10, R j < 2 ^ 36)
    (hB4 : S 4 = R 4) (hh : headK R 10 25920 2 = true)
    (hcO : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true)
    (hp : genPosK R 10 25920 [5, 6, 7] [p₅, p₆, p₇] = true)
    (hc₅ : centInvK (R 2) (R 5) = true) (hc₆ : centInvK (R 2) (R 6) = true)
    (hc₇ : centInvK (R 2) (R 7) = true)
    (hW₀ : W 0 = commK (R 5) (R 6)) (hW₁ : W 1 = commK (R 5) (R 7))
    (hhW : headK W 2 360 2 = true) (hcW : chunkF W (rstG W 0) 2 360 512 0 = true)
    (hdB : hdrC S (R 0) (R 1) (S 4) = true) (hhB : headC S 5 270 = true)
    (hcB : ∀ q < 9, chunkF S (cjG S) 5 270 32 q = true)
    (hcl : clsChunk W 2 360 S 270 S 270 512 0 = true) :
    a6Check () = true := by
  have T := omega_inv hA hB hh hcO
  have look : ∀ i ∈ [5, 6, 7], (Enum.lookup (bfsEnum (genA6 ()) 25920) (arrF (R i))).isSome =
      true := by
    intro i hi
    obtain ⟨p, hp', hpe⟩ := genPosK_sound hp i hi
    have h := lookup_of_inv (T := fun t => arrF (recX R 10 t)) T.1 hp'
    beta_reduce at h
    rw [hpe] at h
    rw [h]
    rfl
  have mc : marr a6cMat = arrF (R 5) := by rw [hc]; rfl
  have m₁ : marr a6d1Mat = arrF (R 6) := by rw [hd₁]; rfl
  have m₂ : marr a6d2Mat = arrF (R 7) := by rw [hd₂]; rfl
  have mr : marr rMat = arrF (R 2) := by rw [hr]; rfl
  have hg : ∀ j < 2, (a6Gens ())[j]! = arrF (W (0 + j)) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · change commArr (marr a6cMat) (marr a6d1Mat) = _
      rw [mc, m₁, commArr_arrF, Nat.add_zero, hW₀]
    · change commArr (marr a6cMat) (marr a6d2Mat) = _
      rw [mc, m₂, commArr_arrF, Nat.zero_add, hW₁]
  have TW := table_invF (gs := a6Gens ()) (R := W) (o := 2) (n := 360) (k := 2) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) hg hhW
    (rows_of_chunks (L := 512) (m := 1)
      (fun q hq => by rw [(by omega : q = 0)]; exact chunkK_of_chunkF hcW) (by norm_num))
  have OB := orbitO (S := S) (fuel := 400) hA hB (by norm_num) (by norm_num) (by norm_num)
    (by rw [hB4]; exact hlt 4 (by norm_num)) hdB hhB hcB
  have mB : marr rBMat = arrF (S 4) := by rw [hrB]; rfl
  rw [a6Check_eq, mc, m₁, m₂, mr, mB, a6Body,
    centInv_arrF (hlt 2 (by norm_num)) (hlt 5 (by norm_num)) (look 5 (by simp)) hc₅,
    centInv_arrF (hlt 2 (by norm_num)) (hlt 6 (by norm_num)) (look 6 (by simp)) hc₆,
    centInv_arrF (hlt 2 (by norm_num)) (hlt 7 (by norm_num)) (look 7 (by simp)) hc₇,
    TW.2.1]
  have hs : ((bfsEnum (a6Gens ()) 360).elems.size == 360) = true := by rw [TW.1.1]; rfl
  rw [hs]
  simp only [Bool.true_and, Array.all_eq_true]
  intro i hi
  have hsz := TW.1.1
  have hi' : i < 360 := by omega
  rw [← getElem!_pos _ i hi, TW.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 1 _
    (fun q hq => by rw [(by omega : q = 0)]; exact hcl) i (by omega)
  change bIf(Nat.blt i 360, strictY (recX W 2 i) (clsAt S 270 S 270), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  have e := clsAt_arrF (TW.2.2 i hi') OB.1 OB.2.2.2 OB.1 OB.2.2.2 hall
  rw [Bool.or_assoc (_ || _), Bool.or_self] at e
  exact e

theorem a6CentCheck_of {RO : ℕ → ℕ} {L m L' m' : ℕ} (hA : aMat = matF (R 0))
    (hB : bMat = matF (R 1)) (hr : rMat = matF (R 2)) (hr2 : R 2 < 2 ^ 36)
    (hc : a6cMat = matF (RO 5)) (hd₁ : a6d1Mat = matF (RO 6)) (hd₂ : a6d2Mat = matF (RO 7))
    (hW₀ : W 0 = commK (RO 5) (RO 6)) (hW₁ : W 1 = commK (RO 5) (RO 7)) (hm : 51840 ≤ L * m)
    (hh : headK R 3 51840 3 = true) (hcO : ∀ q < m, chunkF3 R (rstG R 0) 3 51840 L q = true)
    (hm' : 51840 ≤ L' * m') (hcl : ∀ q < m', a6cChunk R 3 51840 (W 0) (W 1) (R 2) L' q = true) :
    a6CentCheck () = true := by
  have T := oEnum_inv hA hB hr hm hh hcO
  have mc : marr a6cMat = arrF (RO 5) := by rw [hc]; rfl
  have m₁ : marr a6d1Mat = arrF (RO 6) := by rw [hd₁]; rfl
  have m₂ : marr a6d2Mat = arrF (RO 7) := by rw [hd₂]; rfl
  have mr : marr rMat = arrF (R 2) := by rw [hr]; rfl
  have g₀ : (a6Gens ())[0]! = arrF (W 0) := by
    change commArr (marr a6cMat) (marr a6d1Mat) = _
    rw [mc, m₁, commArr_arrF, hW₀]
  have g₁ : (a6Gens ())[1]! = arrF (W 1) := by
    change commArr (marr a6cMat) (marr a6d2Mat) = _
    rw [mc, m₂, commArr_arrF, hW₁]
  have l₀ : W 0 < 2 ^ 36 := by rw [hW₀]; exact CFSG.KC.Sp62.MULF_lt _ _
  have l₁ : W 1 < 2 ^ 36 := by rw [hW₁]; exact CFSG.KC.Sp62.MULF_lt _ _
  rw [a6CentCheck_eq, g₀, g₁, mr, a6CentBody, Array.all_eq_true]
  intro i hi
  have hsz := T.1.1
  have hi' : i < 51840 := by omega
  rw [← getElem!_pos _ i hi, T.1.2.2.2.1 i hi']
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks L' m' _ hcl i (by omega)
  change bIf(Nat.blt i 51840, strictY (recX R 3 i) (a6cAt (W 0) (W 1) (R 2)), true) = true at hall
  rw [Nat.blt_eq.mpr hi', strictY_eq] at hall
  rw [a6cAt_arrF l₀ l₁ hr2 (T.2 i hi')]
  exact hall

end Checks

end CFSG.KC.OmegaSix

end
