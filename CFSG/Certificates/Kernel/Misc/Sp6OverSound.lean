module

public import Certificates.Data.Kernel.Misc.Sp6Over
public import Certificates.Data.RudvalisFF81Sp6Over
public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Quasithin.H13.L32NMatNGen
public import CFSG.Certificates.Kernel.Misc.BfsKSound

public section

namespace CFSG.KC.Sp6Over

open CFSG.KD.Sp6Over CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.LQT.P CFSG.KC.Ord
  CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.Quasithin.G2U

@[expose] def digs (w : List ℕ) : ℕ := w.foldr (fun d acc => d + 4 * acc) 0

@[expose] def encW (w : List ℕ) : ℕ := w.length + 16 * digs w

@[expose] def encR (r : List ℕ × ℕ) : ℕ := r.2 + 16 * encW r.1

@[expose] def wordL : List (List ℕ) := [wZ0, wZ1, wT] ++ wS ++ [[0, 1, 2], wP1]

@[expose] def tgtL : List (List ℕ) := [zCode 0, zCode 1, tCode] ++ sylowP.map Prod.fst

@[expose] def codes6 : List (List ℕ) := [ovGamC, ovGamI, ovHC, ovHI, ovCC, ovCI]

@[expose] def HdrOK (R : ℕ → ℕ) : Prop :=
  (∀ i < 6, R (34 + i) = pk (codes6.getD i [])) ∧
  trC 6 (R 34) = pk (tr6 ovGamC) ∧ trC 6 (R 36) = pk (tr6 ovHC) ∧ trC 6 (R 38) = pk (tr6 ovCC) ∧
  (∀ i < 8, R (40 + i) = pk (tgtL.getD i [])) ∧
  (∀ i < 10, R (48 + i) = encW (wordL.getD i [])) ∧
  (∀ i < 13, R (21 + i) = encR (relW.getD i ([], 0)))

noncomputable instance (R : ℕ → ℕ) : Decidable (HdrOK R) := by unfold HdrOK; infer_instance

theorem land_low {k v : ℕ} (m : ℕ) (hk : k < 2 ^ m) : Nat.land (k + 2 ^ m * v) (2 ^ m - 1) = k := by
  change (k + 2 ^ m * v) &&& (2 ^ m - 1) = k
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

theorem shr_high {k v : ℕ} (m : ℕ) (hk : k < 2 ^ m) : Nat.shiftRight (k + 2 ^ m * v) m = v := by
  change (k + 2 ^ m * v) >>> m = v
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos m),
    Nat.div_eq_of_lt hk, Nat.zero_add]

theorem wordM_cons (mul : ℕ → ℕ → ℕ) (one : ℕ) (G : ℕ → ℕ) {d : ℕ} (hd : d < 4) (len v : ℕ) :
    wordM mul one G (len + 1) (d + 4 * v) = mul (G d) (wordM mul one G len v) := by
  change mul (G (Nat.land (d + 2 ^ 2 * v) (2 ^ 2 - 1)))
    (wordM mul one G len (Nat.shiftRight (d + 2 ^ 2 * v) 2)) = _
  rw [land_low 2 hd, shr_high 2 hd]

theorem land16 {k v : ℕ} (hk : k < 16) : Nat.land (k + 16 * v) 15 = k := land_low 4 hk

theorem shr16 {k v : ℕ} (hk : k < 16) : Nat.shiftRight (k + 16 * v) 4 = v := shr_high 4 hk

theorem wordW_encW (mul : ℕ → ℕ → ℕ) (one : ℕ) (G : ℕ → ℕ) {w : List ℕ} (hw : w.length < 16) :
    wordW mul one G (encW w) = wordM mul one G w.length (digs w) := by
  unfold wordW encW
  rw [land16 hw, shr16 hw]

theorem relOK_encR (mul : ℕ → ℕ → ℕ) (one : ℕ) (G : ℕ → ℕ) {r : List ℕ × ℕ} (hk : r.2 < 16)
    (hw : r.1.length < 16) :
    relOK mul one G (encR r) =
      Nat.beq (powM mul one (wordM mul one G r.1.length (digs r.1)) r.2) one := by
  unfold relOK encR
  rw [letB_eq, shr16 hk, land16 hk, wordW_encW mul one G hw]

theorem allUp_from (f : ℕ → Bool) : ∀ m i, Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih i => andB (f i) (ih (Nat.succ i))) m i = true ↔ ∀ j < m, f (i + j) = true
  | 0, i => by simp
  | m + 1, i => by
    change andB (f i) (Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun _ ih i => andB (f i) (ih (Nat.succ i))) m (i + 1)) = true ↔ _
    rw [andB_iff, allUp_from f m (i + 1)]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · exact h0
      · have := h j (by omega)
        rwa [show i + 1 + j = i + (j + 1) by omega] at this
    · intro h
      exact ⟨h 0 (by omega), fun j hj => by
        have := h (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this⟩

theorem allUp_iff (m : ℕ) (f : ℕ → Bool) : allUp m f = true ↔ ∀ j < m, f j = true := by
  unfold allUp
  rw [allUp_from]
  simp

section H6

variable {A B C : ℕ}

theorem gen_pk (hA : pk ovGamC = A) (hB : pk ovHC = B) (hC : pk ovCC = C) {d : ℕ} (hd : d < 3) :
    canon6 (genC.getD d one6) = true ∧ pk (genC.getD d one6) = gen3 A B C d := by
  match d, hd with
  | 0, _ => exact ⟨by decide, hA⟩
  | 1, _ => exact ⟨by decide, hB⟩
  | 2, _ => exact ⟨by decide, hC⟩

theorem wordC_pk (hA : pk ovGamC = A) (hB : pk ovHC = B) (hC : pk ovCC = C) :
    ∀ w : List ℕ, (∀ d ∈ w, d < 3) → canon6 (wordC w) = true ∧
      pk (wordC w) = wordM MULF ONE (gen3 A B C) w.length (digs w)
  | [], _ => one_pk
  | d :: w, hw => by
    have hd : d < 3 := hw d (List.mem_cons_self ..)
    have ih := wordC_pk hA hB hC w fun e he => hw e (List.mem_cons_of_mem _ he)
    have e : wordC (d :: w) = mul6 (genC.getD d one6) (wordC w) := rfl
    rw [e, List.length_cons, digs, List.foldr_cons, ← digs, wordM_cons _ _ _ (by omega)]
    exact mulE (gen_pk hA hB hC hd) ih

theorem canon6_tgtL : ∀ i < 8, canon6 (tgtL.getD i []) = true := by decide

theorem wordL_ok : ∀ i < 10, (∀ d ∈ wordL.getD i [], d < 3) ∧ (wordL.getD i []).length < 16 := by
  decide

theorem relW_ok : ∀ i < 13, (∀ d ∈ (relW.getD i ([], 0)).1, d < 3) ∧
    (relW.getD i ([], 0)).1.length < 16 ∧ (relW.getD i ([], 0)).2 < 16 := by
  decide

theorem relW_length : relW.length = 13 := rfl

theorem wS_length : wS.length = 5 := rfl

theorem sylowP_length : sylowP.length = 5 := rfl

theorem h6_facts {R : ℕ → ℕ} (hR : HdrOK R) (h : h6K R = true) :
    pairCheck (ovGamC, ovGamI) = true ∧ pairCheck (ovHC, ovHI) = true ∧
    pairCheck (ovCC, ovCI) = true ∧ relW.all (fun r => powCode (wordC r.1) r.2 == one6) = true ∧
    powCode ovGamC 7 = one6 ∧ ovGamC ≠ one6 ∧ powCode ovHC 6 = one6 ∧
    mul6 ovHC ovGamC = mul6 (powCode ovGamC 3) ovHC ∧
    mul6 ovCC (mul6 ovHC ovHC) = mul6 (mul6 ovHC ovHC) ovCC ∧
    wordC wZ0 = zCode 0 ∧ wordC wZ1 = zCode 1 ∧ wordC wT = tCode ∧
    wS.map wordC = sylowP.map Prod.fst ∧ powCode (wordC [0, 1, 2]) 5 = one6 ∧
    wordC [0, 1, 2] ≠ one6 := by
  obtain ⟨hc, hT0, hT1, hT2, htg, hwd, hrl⟩ := hR
  have c0 := hc 0 (by omega)
  have c1 := hc 1 (by omega)
  have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega)
  have c4 := hc 4 (by omega)
  have c5 := hc 5 (by omega)
  simp only [codes6, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3 c4 c5
  have eA : pk ovGamC = R 34 := c0.symm
  have eB : pk ovHC = R 36 := c2.symm
  have eC : pk ovCC = R 38 := c4.symm
  have kA : canon6 ovGamC = true := by decide
  have kB : canon6 ovHC = true := by decide
  have kC : canon6 ovCC = true := by decide
  have hW : ∀ i < 10, canon6 (wordC (wordL.getD i [])) = true ∧
      pk (wordC (wordL.getD i [])) = wordW MULF ONE (gen3 (R 34) (R 36) (R 38)) (R (48 + i)) := by
    intro i hi
    obtain ⟨hl, hn⟩ := wordL_ok i hi
    rw [hwd i hi, wordW_encW _ _ _ hn]
    exact wordC_pk eA eB eC _ hl
  unfold h6K at h
  simp only [letB_eq, andB_iff, notB_iff, beq_iff, allUp_iff, allN_iff] at h
  obtain ⟨⟨p1, p2, p3⟩, hrel, ⟨g7, gne, h6⟩, ⟨hconj, hcomm⟩, hwords, y5, yne⟩ := h
  have hwords' : ∀ i < 8, wordW MULF ONE (gen3 (R 34) (R 36) (R 38)) (R (48 + i)) =
      R (40 + i) := hwords
  have Y := hW 8 (by omega)
  have g8 : wordL.getD 8 [] = [0, 1, 2] := rfl
  rw [g8] at Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairCheck_eq ⟨kA, eA⟩ ⟨by decide, c1.symm⟩ ⟨by decide, hT0.symm⟩]
    exact p1
  · rw [pairCheck_eq ⟨kB, eB⟩ ⟨by decide, c3.symm⟩ ⟨by decide, hT1.symm⟩]
    exact p2
  · rw [pairCheck_eq ⟨kC, eC⟩ ⟨by decide, c5.symm⟩ ⟨by decide, hT2.symm⟩]
    exact p3
  · rw [List.all_eq_true]
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hgi : relW[i] = relW.getD i ([], 0) := (List.getD_eq_getElem _ _ hi).symm
    rw [hgi]
    replace hi : i < 13 := relW_length ▸ hi
    have e : relOK MULF ONE (gen3 (R 34) (R 36) (R 38)) (R (21 + i)) = true := hrel i hi
    obtain ⟨hl, hn, hk⟩ := relW_ok i hi
    rw [hrl i hi, relOK_encR _ _ _ hk hn] at e
    have hw := wordC_pk eA eB eC _ hl
    have hp := powCode_pk hw (relW.getD i ([], 0)).2
    rw [beq_pk hp.1 canon6_one6, hp.2, pk_one6]
    exact e
  · have hp := powCode_pk ⟨kA, eA⟩ 7
    exact pk_inj hp.1 canon6_one6 (by rw [hp.2, pk_one6]; exact g7)
  · intro e
    exact gne (by rw [← eA, e, pk_one6])
  · have hp := powCode_pk ⟨kB, eB⟩ 6
    exact pk_inj hp.1 canon6_one6 (by rw [hp.2, pk_one6]; exact h6)
  · have h1 := mulE ⟨kB, eB⟩ ⟨kA, eA⟩
    have h2 := mulE (powCode_pk ⟨kA, eA⟩ 3) ⟨kB, eB⟩
    exact pk_inj h1.1 h2.1 (by rw [h1.2, h2.2]; exact hconj)
  · have hBB := mulE ⟨kB, eB⟩ ⟨kB, eB⟩
    have h1 := mulE ⟨kC, eC⟩ hBB
    have h2 := mulE hBB ⟨kC, eC⟩
    exact pk_inj h1.1 h2.1 (by rw [h1.2, h2.2]; exact hcomm)
  · have Wi := hW 0 (by omega)
    have t := htg 0 (by omega)
    have e := hwords' 0 (by omega)
    exact pk_inj Wi.1 (canon6_tgtL 0 (by omega)) (Wi.2.trans (e.trans t))
  · have Wi := hW 1 (by omega)
    have t := htg 1 (by omega)
    have e := hwords' 1 (by omega)
    exact pk_inj Wi.1 (canon6_tgtL 1 (by omega)) (Wi.2.trans (e.trans t))
  · have Wi := hW 2 (by omega)
    have t := htg 2 (by omega)
    have e := hwords' 2 (by omega)
    exact pk_inj Wi.1 (canon6_tgtL 2 (by omega)) (Wi.2.trans (e.trans t))
  · apply List.ext_getElem (by rw [List.length_map, List.length_map, wS_length, sylowP_length])
    intro i h1 h2
    rw [List.length_map, wS_length] at h1
    have Wi := hW (3 + i) (by omega)
    have t := htg (3 + i) (by omega)
    have e := hwords' (3 + i) (by omega)
    have kt := canon6_tgtL (3 + i) (by omega)
    have g1 : wordL.getD (3 + i) [] = wS[i] := by interval_cases i <;> rfl
    have g2 : tgtL.getD (3 + i) [] = (sylowP.map Prod.fst)[i] := by interval_cases i <;> rfl
    rw [g1] at Wi
    rw [g2] at t kt
    rw [List.getElem_map (f := wordC)]
    exact pk_inj Wi.1 kt (Wi.2.trans (e.trans t))
  · have hp := powCode_pk Y 5
    exact pk_inj hp.1 canon6_one6 (by rw [hp.2, pk_one6]; exact y5)
  · intro e
    exact yne (by rw [← Y.2, e, pk_one6])

end H6

section Packed

open CFSG.Quasithin.H13.MatNCert CFSG.KC.Misc.Spec CFSG.KC.Misc.G24

variable {n : ℕ}

@[expose] def colC (n X j : ℕ) : ℕ := (X >>> (n * j)) &&& (2 ^ n - 1)

theorem colC_cons {c : ℕ} (hc : c < 2 ^ n) (Y : ℕ) :
    colC n (c + 2 ^ n * Y) 0 = c ∧ ∀ j, colC n (c + 2 ^ n * Y) (j + 1) = colC n Y j := by
  have hs : (c + 2 ^ n * Y) >>> n = Y := shr_high n hc
  refine ⟨?_, fun j => ?_⟩
  · unfold colC
    rw [Nat.mul_zero, Nat.shiftRight_zero]
    exact land_low n hc
  · unfold colC
    rw [Nat.mul_succ, Nat.add_comm (n * j) n, Nat.shiftRight_add, hs]

theorem colC_codeL : ∀ {A : List ℕ}, (∀ c ∈ A, c < 2 ^ n) → ∀ j,
    colC n (codeL n A) j = A.getD j 0
  | [], _, j => by simp [codeL, colC]
  | c :: A, hA, j => by
    have hc := hA c (List.mem_cons_self ..)
    have e : codeL n (c :: A) = c + 2 ^ n * codeL n A := rfl
    rw [e]
    rcases j with _ | j
    · exact (colC_cons hc _).1
    · rw [(colC_cons hc _).2 j, colC_codeL (fun d hd => hA d (List.mem_cons_of_mem _ hd)) j]
      rfl

theorem testBit_colC (X j i : ℕ) :
    (colC n X j).testBit i = (decide (i < n) && X.testBit (n * j + i)) := by
  unfold colC
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem codeL_lt : ∀ {A : List ℕ}, (∀ c ∈ A, c < 2 ^ n) → codeL n A < 2 ^ (n * A.length)
  | [], _ => by simp [codeL]
  | c :: A, hA => by
    have hc := hA c (List.mem_cons_self ..)
    have ih := codeL_lt fun d hd => hA d (List.mem_cons_of_mem _ hd)
    have e : codeL n (c :: A) = c + 2 ^ n * codeL n A := rfl
    rw [e, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (n * A.length))]
    calc c + 2 ^ n * codeL n A < 2 ^ n + 2 ^ n * codeL n A := by omega
      _ = 2 ^ n * (codeL n A + 1) := by ring
      _ ≤ 2 ^ n * 2 ^ (n * A.length) := Nat.mul_le_mul_left _ ih

theorem pkMat_codeL {A : List ℕ} (hA : ValidN n A) : pkMat n (codeL n A) = (decN n A).transpose := by
  ext i j
  simp only [pkMat, decN, Matrix.transpose_apply, Matrix.of_apply, vecN]
  have h := testBit_colC (n := n) (codeL n A) i j
  rw [colC_codeL hA.2, decide_eq_true j.isLt, Bool.true_and] at h
  rw [← h]
  rfl

theorem pkMat_inj' {A B : ℕ} (hA : A < 2 ^ (n * n)) (hB : B < 2 ^ (n * n))
    (h : pkMat n A = pkMat n B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < n * n
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hp
      · exact h
    have hq : p / n < n := Nat.div_lt_of_lt_mul hp
    have := congrFun (congrFun h ⟨p / n, hq⟩) ⟨p % n, Nat.mod_lt _ hn⟩
    simp only [pkMat, Matrix.of_apply] at this
    rw [Nat.div_add_mod] at this
    exact ite_inj _ _ this
  · have h2 : 2 ^ (n * n) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem stepF2_lt (hn : 0 < n) (A B k : ℕ) : stepF2 n A B k < 2 ^ (n * n) := by
  have hm := repu_mul n n
  have hV : (B >>> (n * k)) &&& (2 ^ n - 1) ≤ 2 ^ n - 1 := Nat.and_le_right
  have hp : 0 < 2 ^ (n * n) := Nat.two_pow_pos _
  calc stepF2 n A B k ≤ ((B >>> (n * k)) &&& (2 ^ n - 1)) * repu n n := Nat.and_le_right
    _ ≤ (2 ^ n - 1) * repu n n := Nat.mul_le_mul_right _ hV
    _ < 2 ^ (n * n) := by omega

theorem mulF2_lt (hn : 0 < n) (A B : ℕ) : mulF2 n A B < 2 ^ (n * n) := by
  rw [mulF2_eq_fold hn]
  have : ∀ m, foldF2 n A B m < 2 ^ (n * n) := by
    intro m
    induction m with
    | zero => exact Nat.two_pow_pos _
    | succ m ih => exact Nat.xor_lt_two_pow ih (stepF2_lt hn A B m)
  exact this n

theorem codeL_lt' {A : List ℕ} (hA : ValidN n A) : codeL n A < 2 ^ (n * n) := by
  have := codeL_lt hA.2
  rwa [hA.1] at this

theorem codeL_mulN (hn : 0 < n) {A B : List ℕ} (hA : ValidN n A) (hB : ValidN n B) :
    codeL n (mulN A B) = mulC n (codeL n A) (codeL n B) := by
  apply pkMat_inj' (codeL_lt' (validN_mulN hA hB)) (mulF2_lt hn _ _)
  rw [pkMat_mulF2, pkMat_codeL (validN_mulN hA hB), pkMat_codeL hA, pkMat_codeL hB,
    decN_mulN hA.1 hB.1, Matrix.transpose_mul]

theorem codeL_inj {A B : List ℕ} (hA : ValidN n A) (hB : ValidN n B)
    (h : codeL n A = codeL n B) : A = B := by
  apply decN_injOn hA hB
  rw [← Matrix.transpose_transpose (decN n A), ← pkMat_codeL hA, h, pkMat_codeL hB,
    Matrix.transpose_transpose]

theorem beq_codeL {A B : List ℕ} (hA : ValidN n A) (hB : ValidN n B) :
    (A == B) = Nat.beq (codeL n A) (codeL n B) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, codeL_inj hA hB⟩

end Packed

section Lists

open CFSG.Quasithin.H13.MatNCert
open CFSG.Quasithin.H13.Mat8Cert (b2z b2z_xor b2z_inj)

variable {n : ℕ}

theorem bitN_eq (x i : ℕ) : bitN x i = if x.testBit i then 1 else 0 := by
  have h1 : bitN x i = x / 2 ^ i % 2 := by
    change (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem mskN_eq (n : ℕ) : mskN n = 2 ^ n - 1 := by
  change 1 <<< n - 1 = _
  rw [Nat.one_shiftLeft]

@[expose] noncomputable def mvCm (n X v m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.xor acc
    (Nat.mul (bitN v j) (Nat.land (Nat.shiftRight X (Nat.mul n j)) (mskN n)))) m

theorem mvCm_succ (n X v m : ℕ) :
    mvCm n X v (m + 1) = mvCm n X v m ^^^ bitN v m * colC n X m := by
  change mvCm n X v m ^^^ bitN v m * ((X >>> (n * m)) &&& mskN n) = _
  rw [mskN_eq]
  rfl

theorem b2z_mvCm (X v i : ℕ) : ∀ m, b2z ((mvCm n X v m).testBit i) =
    ∑ j ∈ Finset.range m, b2z (v.testBit j) * b2z ((colC n X j).testBit i)
  | 0 => by simp [mvCm, b2z]
  | m + 1 => by
    rw [mvCm_succ, Finset.sum_range_succ, Nat.testBit_xor, b2z_xor, b2z_mvCm X v i m, bitN_eq]
    cases v.testBit m <;> simp [b2z]

theorem mvC_codeL {A : List ℕ} (hA : ValidN n A) (v : ℕ) : mvC n (codeL n A) v = mvN A v := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply b2z_inj
  rw [b2z_testBit_mvN, hA.1]
  change b2z ((mvCm n (codeL n A) v n).testBit i) = _
  rw [b2z_mvCm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colC_codeL hA.2]

theorem mvN_congr {L L' : List ℕ} (hl : L.length = L'.length) {x : ℕ}
    (h : ∀ j, x.testBit j = true → L.getD j 0 = L'.getD j 0) : mvN L x = mvN L' x := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply b2z_inj
  rw [b2z_testBit_mvN, b2z_testBit_mvN, hl]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases hj : x.testBit j
  · simp [b2z]
  · rw [h j hj]

theorem mvN_oneN {y : ℕ} (hy : y < 2 ^ n) : mvN (oneN n) y = y := by
  have h := decN_mulVec (n := n) (A := oneN n) validN_oneN.1 y
  rw [decN_oneN, Matrix.one_mulVec] at h
  exact vecN_inj (mvN_lt validN_oneN.2 y) hy h.symm

theorem mulN_oneN {X : List ℕ} (hX : ValidN n X) : mulN X (oneN n) = X := by
  apply decN_injOn (validN_mulN hX validN_oneN) hX
  rw [decN_mulN hX.1 validN_oneN.1, decN_oneN, mul_one]

theorem validN_powN' {X : List ℕ} (hX : ValidN n X) : ∀ k, ValidN n (powN n X k)
  | 0 => validN_oneN
  | k + 1 => validN_mulN hX (validN_powN' hX k)

theorem decN_powN {X : List ℕ} (hX : ValidN n X) : ∀ k, decN n (powN n X k) = decN n X ^ k
  | 0 => by rw [pow_zero]; exact decN_oneN
  | k + 1 => by
    change decN n (mulN X (powN n X k)) = _
    rw [decN_mulN hX.1 (validN_powN' hX k).1, decN_powN hX k, pow_succ']

theorem mulN_powN {X : List ℕ} (hX : ValidN n X) (k : ℕ) :
    mulN (powN n X k) X = powN n X (k + 1) := by
  apply decN_injOn (validN_mulN (validN_powN' hX k) hX) (validN_powN' hX (k + 1))
  rw [decN_mulN (validN_powN' hX k).1 hX.1, decN_powN hX, decN_powN hX, pow_succ]

theorem mvN_powN {X : List ℕ} {y : ℕ} (hy : y < 2 ^ n) : ∀ k,
    mvN (powN n X k) y = Nat.rec (motive := fun _ => ℕ) y (fun _ z => mvN X z) k
  | 0 => mvN_oneN hy
  | k + 1 => by
    change mvN (mulN X (powN n X k)) y = mvN X _
    rw [mvN_mulN, mvN_powN hy k]

theorem powM_codeL (hn : 0 < n) {X : List ℕ} (hX : ValidN n X) : ∀ k,
    powM (mulC n) (codeL n (oneN n)) (codeL n X) k = codeL n (powN n X k)
  | 0 => rfl
  | k + 1 => by
    change mulC n (powM (mulC n) (codeL n (oneN n)) (codeL n X) k) (codeL n X) = _
    rw [powM_codeL hn hX k, ← codeL_mulN hn (validN_powN' hX k) hX, mulN_powN hX]

theorem gen3_codeL (a b c : List ℕ) {d : ℕ} (hd : d < 3) :
    gen3 (codeL n a) (codeL n b) (codeL n c) d = codeL n ([a, b, c].getD d (oneN n)) := by
  match d, hd with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem wordM_codeL (hn : 0 < n) {a b c : List ℕ} (ha : ValidN n a) (hb : ValidN n b)
    (hc : ValidN n c) : ∀ w : List ℕ, (∀ d ∈ w, d < 3) →
    wordM (mulC n) (codeL n (oneN n)) (gen3 (codeL n a) (codeL n b) (codeL n c)) w.length
      (digs w) = codeL n (evalW n [a, b, c] w)
  | [], _ => rfl
  | d :: w, hw => by
    have hd : d < 3 := hw d (List.mem_cons_self ..)
    have ih := wordM_codeL hn ha hb hc w fun e he => hw e (List.mem_cons_of_mem _ he)
    have hg : ∀ g ∈ [a, b, c], ValidN n g := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl | rfl) <;> assumption
    rw [List.length_cons, digs, List.foldr_cons, ← digs, wordM_cons _ _ _ (by omega), ih,
      evalW_cons, gen3_codeL a b c hd, codeL_mulN hn (validN_getD hg d) (validN_evalW _ hg w)]

end Lists

section Pin

open CFSG.Quasithin.H13.MatNCert
open CFSG.Quasithin.H13.Mat8Cert (b2z b2z_xor b2z_inj)

@[expose] def PinHdr (R : ℕ → ℕ) : Prop :=
  R 17 = codeL 7 nGc ∧ R 18 = codeL 7 nHc ∧ R 19 = codeL 7 xSc ∧ R 20 = codeL 7 xIc

noncomputable instance (R : ℕ → ℕ) : Decidable (PinHdr R) := by unfold PinHdr; infer_instance

theorem validN_nGc : ValidN 7 nGc := by unfold ValidN; decide

theorem validN_nHc : ValidN 7 nHc := by unfold ValidN; decide

theorem validN_xSc : ValidN 7 xSc := by unfold ValidN; decide

theorem validN_xIc : ValidN 7 xIc := by unfold ValidN; decide

theorem validN_n2c : ValidN 7 n2c := validN_mulN validN_nHc validN_nHc

theorem ONE7_eq : ONE7 = codeL 7 (oneN 7) := by decide +kernel

theorem fixL_eq : fixL = (List.range 8).map fA := by decide +kernel

theorem wL_eq : wL = (List.range 16).map wV := by decide +kernel

theorem fixL_complete : ∀ c < 128, Nat.land c 108 = 0 → c ∈ fixL := by decide +kernel

theorem wL_complete : ∀ c < 128, wV (wCo c) = c → c ∈ wL := by decide +kernel

theorem fixL_lt : ∀ x ∈ fixL, x < 2 ^ 7 := by decide

theorem wL_lt : ∀ x ∈ wL, x < 2 ^ 7 := by decide

theorem wL_xor : ∀ x ∈ wL, ∀ y ∈ wL, x ^^^ y ∈ wL := by decide +kernel

theorem wL_n2c : ∀ x ∈ wL, mvN n2c x ∈ wL := by decide +kernel

theorem fixL_cand : ∀ a ∈ fixL, ∀ b ∈ fixL, ∀ x ∈ fixL,
    mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a 0 b 0) x ∈ fixL := by
  decide +kernel

theorem fixL_bits : ∀ x ∈ fixL, ∀ j, x.testBit j = true → j = 0 ∨ j = 1 ∨ j = 4 := by
  intro x hx j hj
  have h19 : ∀ y ∈ fixL, y &&& 19 = y := by decide
  rw [← h19 x hx, Nat.testBit_and, Bool.and_eq_true] at hj
  have hj5 : j < 5 := by
    by_contra hc
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 19 < 2 ^ 5)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hj
    exact Bool.false_ne_true hj.2
  have h2 := hj.2
  interval_cases j <;> first | omega | (revert h2; decide)

theorem validN_cand {a u b v : ℕ} (ha : a < 2 ^ 7) (hu : u < 2 ^ 7) (hb : b < 2 ^ 7)
    (hv : v < 2 ^ 7) : ValidN 7 (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) := by
  refine ⟨rfl, ?_⟩
  have hx := mvN_lt validN_n2c.2 u
  have hz := mvN_lt validN_n2c.2 v
  simp only [CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · norm_num
  · exact ha
  · exact hu
  · exact hx
  · exact hb
  · exact Nat.xor_lt_two_pow hv hb
  · exact Nat.xor_lt_two_pow hz hb

theorem add_pow_mul_eq_or {k c : ℕ} (hc : c < 2 ^ k) (Y : ℕ) : c + 2 ^ k * Y = c ||| Y <<< k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hc, Nat.shiftLeft_eq]
  ring

theorem cand_num {a u b v : ℕ} (ha : a < 2 ^ 7) (hu : u < 2 ^ 7) (hb : b < 2 ^ 7)
    (hv : v < 2 ^ 7) : CFSG.KD.Sp6Over.cand (codeL 7 n2c) a u b v =
      codeL 7 (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) := by
  have hx := mvN_lt validN_n2c.2 u
  have hz := mvN_lt validN_n2c.2 v
  have hy := Nat.xor_lt_two_pow hv hb
  have hw := Nat.xor_lt_two_pow hz hb
  unfold CFSG.KD.Sp6Over.cand CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand
  rw [mvC_codeL validN_n2c, mvC_codeL validN_n2c]
  simp only [codeL, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
  rw [add_pow_mul_eq_or (k := 7) (c := 1) (by norm_num), add_pow_mul_eq_or ha,
    add_pow_mul_eq_or hu, add_pow_mul_eq_or hx, add_pow_mul_eq_or hb, add_pow_mul_eq_or hy]
  simp only [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.lor_eq, Nat.xor_eq,
    Nat.shiftLeft_eq', Nat.reduceAdd]

theorem bitB_maskOf (f : ℕ → Bool) : ∀ m i, i < m → bitB (maskOf m f) i = f i := by
  have key : ∀ m i, (maskOf m f).testBit i = (decide (i < m) && f i) := by
    intro m
    induction m with
    | zero => intro i; simp [maskOf]
    | succ m ih =>
      intro i
      change (Nat.lor (maskOf m f) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft 1 m)
        (f m))).testBit i = _
      rw [Nat.lor_eq, Nat.testBit_or, ih]
      by_cases hi : i = m
      · subst hi
        cases f i <;> simp [Nat.one_shiftLeft]
      · have e : decide (i < m + 1) = decide (i < m) := by
          rw [decide_eq_decide]
          omega
        rw [e]
        cases f m <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hi]
  intro m i hi
  unfold bitB
  rw [bitN_eq, key, decide_eq_true hi, Bool.true_and]
  cases f i <;> rfl

theorem fix6_codeL {L : List ℕ} (hL : ValidN 7 L) (x : ℕ) :
    fix6 (codeL 7 L) x = true ↔ Nat.rec (motive := fun _ => ℕ) x (fun _ y => mvN L y) 6 = x := by
  unfold fix6
  rw [beq_iff]
  simp only [mvC_codeL hL]

theorem rec_congr (f g : ℕ → ℕ) (S : ℕ → Prop) (h : ∀ y, S y → f y = g y ∧ S (g y)) :
    ∀ k x, S x → Nat.rec (motive := fun _ => ℕ) x (fun _ y => f y) k =
      Nat.rec (motive := fun _ => ℕ) x (fun _ y => g y) k ∧
      S (Nat.rec (motive := fun _ => ℕ) x (fun _ y => g y) k)
  | 0, _, hx => ⟨rfl, hx⟩
  | k + 1, x, hx => by
    obtain ⟨e, hs⟩ := rec_congr f g S h k x hx
    obtain ⟨e', hs'⟩ := h _ hs
    exact ⟨by change f _ = g _; rw [e, e'], hs'⟩

theorem pow6_of_relsOK {X : List ℕ} (hX : ValidN 7 X)
    (h : CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.relsOK X = true) : powN 7 X 6 = oneN 7 := by
  have h0 : (powN 7 (evalW 7 [nGc, nHc, X] [2]) 6 == oneN 7) = true :=
    List.all_eq_true.1 h ([2], 6) (by decide)
  have e : evalW 7 [nGc, nHc, X] [2] = mulN X (oneN 7) := rfl
  rw [e, mulN_oneN hX, beq_iff_eq] at h0
  exact h0

theorem rec6_of_relsOK {X : List ℕ} (hX : ValidN 7 X)
    (h : CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.relsOK X = true) {y : ℕ} (hy : y < 2 ^ 7) :
    Nat.rec (motive := fun _ => ℕ) y (fun _ z => mvN X z) 6 = y := by
  rw [← mvN_powN hy, pow6_of_relsOK hX h, mvN_oneN hy]

theorem relsK_of {R : ℕ → ℕ} (hR : HdrOK R) {X : List ℕ} (hX : ValidN 7 X)
    (h : CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.relsOK X = true) :
    relsK R (codeL 7 nGc) (codeL 7 nHc) (codeL 7 X) = true := by
  obtain ⟨-, -, -, -, -, -, hrl⟩ := hR
  unfold relsK
  rw [allUp_iff]
  intro i hi
  change relOK (mulC 7) ONE7 _ (R (21 + i)) = true
  obtain ⟨hl, hn, hk⟩ := relW_ok i hi
  have hmem : relW.getD i ([], 0) ∈ relW :=
    List.getD_eq_getElem _ _ (relW_length ▸ hi) ▸ List.getElem_mem _
  have hr : (powN 7 (evalW 7 [nGc, nHc, X] (relW.getD i ([], 0)).1) (relW.getD i ([], 0)).2 ==
      oneN 7) = true := List.all_eq_true.1 h _ hmem
  have hE := validN_evalW (n := 7) [nGc, nHc, X] (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl)
    · exact validN_nGc
    · exact validN_nHc
    · exact hX) (relW.getD i ([], 0)).1
  rw [hrl i hi, relOK_encR _ _ _ hk hn, ONE7_eq,
    wordM_codeL (by norm_num) validN_nGc validN_nHc hX _ hl, powM_codeL (by norm_num) hE,
    ← beq_codeL (validN_powN' hE _) validN_oneN]
  exact hr

theorem cand_fixL (a u b v : ℕ) {x : ℕ} (hx : x ∈ fixL) :
    mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) x =
      mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a 0 b 0) x := by
  refine mvN_congr ?_ fun j hj => ?_
  · rfl
  rcases fixL_bits x hx j hj with rfl | rfl | rfl <;> rfl

theorem mvN_cand_eval (c0 c1 c2 c3 c4 c5 c6 : ℕ) :
    mvN [c0, c1, c2, c3, c4, c5, c6] 4 = c2 ∧ mvN [c0, c1, c2, c3, c4, c5, c6] 8 = c3 ∧
    mvN [c0, c1, c2, c3, c4, c5, c6] 48 = c4 ^^^ c5 ∧
    mvN [c0, c1, c2, c3, c4, c5, c6] 80 = c4 ^^^ c6 := by
  simp [mvN, Nat.testBit_zero]

theorem wL_induct (P : ℕ → Prop) (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b)) (h4 : P 4)
    (h8 : P 8) (h48 : P 48) (h80 : P 80) : ∀ y ∈ wL, P y := by
  intro y hy
  rw [wL_eq] at hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  have hb : ∀ t c, P c → P (bitN j t * c) := by
    intro t c hc
    rw [bitN_eq]
    split
    · rwa [Nat.one_mul]
    · rwa [Nat.zero_mul]
  exact hx _ _ (hx _ _ (hb 0 4 h4) (hb 1 8 h8)) (hx _ _ (hb 2 48 h48) (hb 3 80 h80))

theorem cand_wL {a u b v : ℕ} (hu : u ∈ wL) (hv : v ∈ wL) : ∀ y ∈ wL,
    mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) y =
      mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand 0 u 0 v) y ∧
    mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand 0 u 0 v) y ∈ wL := by
  have h0 : (0 : ℕ) ∈ wL := by decide
  obtain ⟨e4, e8, e48, e80⟩ := mvN_cand_eval 1 a u (mvN n2c u) b (v ^^^ b) (mvN n2c v ^^^ b)
  obtain ⟨f4, f8, f48, f80⟩ := mvN_cand_eval 1 0 u (mvN n2c u) 0 (v ^^^ 0) (mvN n2c v ^^^ 0)
  apply wL_induct
  · rw [mvN_zero, mvN_zero]
    exact ⟨rfl, h0⟩
  · rintro x y ⟨ex, hx⟩ ⟨ey, hy⟩
    rw [mvN_xor, mvN_xor, ex, ey]
    exact ⟨rfl, wL_xor _ hx _ hy⟩
  · simp only [CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand] at e4 f4 ⊢
    rw [e4, f4]
    exact ⟨rfl, hu⟩
  · simp only [CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand] at e8 f8 ⊢
    rw [e8, f8]
    exact ⟨rfl, wL_n2c _ hu⟩
  · simp only [CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand] at e48 f48 ⊢
    rw [e48, f48, Nat.xor_zero, Nat.zero_xor, ← Nat.xor_assoc, Nat.xor_comm b v, Nat.xor_assoc,
      Nat.xor_self, Nat.xor_zero]
    exact ⟨rfl, hv⟩
  · simp only [CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand] at e80 f80 ⊢
    rw [e80, f80, Nat.xor_zero, Nat.zero_xor, ← Nat.xor_assoc, Nat.xor_comm b, Nat.xor_assoc,
      Nat.xor_self, Nat.xor_zero]
    exact ⟨rfl, wL_n2c _ hv⟩

theorem pin_facts {R : ℕ → ℕ} (hR : HdrOK R) (hP : PinHdr R) (h : pinK R = true) :
    (∀ c < 128, mvN n2c c = c → c ∈ fixL) ∧
    (∀ c < 128, mvN n2c (mvN n2c c) = (c ^^^ mvN n2c c) → c ∈ wL) ∧
    (∀ a ∈ fixL, ∀ u ∈ wL, ∀ b ∈ fixL, ∀ v ∈ wL,
      CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.relsOK
        (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) = true →
      CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xSc ∨
        CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v = xIc) := by
  obtain ⟨h17, h18, h19, h20⟩ := hP
  have eN2 : mulC 7 (codeL 7 nHc) (codeL 7 nHc) = codeL 7 n2c :=
    (codeL_mulN (by norm_num) validN_nHc validN_nHc).symm
  unfold pinK at h
  rw [letB_eq, letB_eq, letB_eq, letB_eq, letB_eq, h17, h18, h19, h20, eN2] at h
  simp only [letB_eq, andB_iff, allN_iff, impB_iff, beq_iff, orB_iff, notB_iff,
    mvC_codeL validN_n2c] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc e => fixL_complete c hc (h1 c hc e),
    fun c hc e => wL_complete c hc (h2 c hc e), ?_⟩
  intro a ha u hu b hb v hv hr
  have la := fixL_lt a ha
  have lb := fixL_lt b hb
  have lu := wL_lt u hu
  have lv := wL_lt v hv
  have hX := validN_cand la lu lb lv
  obtain ⟨i1, hi1, ea⟩ := List.mem_map.1 (fixL_eq ▸ ha)
  obtain ⟨i2, hi2, eb⟩ := List.mem_map.1 (fixL_eq ▸ hb)
  obtain ⟨j1, hj1, eu⟩ := List.mem_map.1 (wL_eq ▸ hu)
  obtain ⟨j2, hj2, ev⟩ := List.mem_map.1 (wL_eq ▸ hv)
  rw [List.mem_range] at hi1 hi2 hj1 hj2
  have q1 : Nat.div (8 * i1 + i2) 8 = i1 := by change (8 * i1 + i2) / 8 = i1; omega
  have q2 : Nat.mod (8 * i1 + i2) 8 = i2 := by change (8 * i1 + i2) % 8 = i2; omega
  have q3 : Nat.div (16 * j1 + j2) 16 = j1 := by change (16 * j1 + j2) / 16 = j1; omega
  have q4 : Nat.mod (16 * j1 + j2) 16 = j2 := by change (16 * j1 + j2) % 16 = j2; omega
  have hA : bitB (maskOf 64 (blockA (codeL 7 n2c))) (8 * i1 + i2) = true := by
    rw [bitB_maskOf _ _ _ (by omega)]
    unfold blockA
    rw [letB_eq, andB_iff, q1, q2, ea, eb, cand_num la (by norm_num) lb (by norm_num),
      fix6_codeL (validN_cand la (by norm_num) lb (by norm_num)),
      fix6_codeL (validN_cand la (by norm_num) lb (by norm_num))]
    have hS : ∀ y, y ∈ fixL →
        mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) y =
          mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a 0 b 0) y ∧
        mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a 0 b 0) y ∈ fixL :=
      fun y hy => ⟨cand_fixL a u b v hy, fixL_cand a ha b hb y hy⟩
    have k2 := rec_congr _ _ _ hS 6 2 (by decide)
    have k16 := rec_congr _ _ _ hS 6 16 (by decide)
    rw [rec6_of_relsOK hX hr (by norm_num)] at k2 k16
    exact ⟨k2.1.symm, k16.1.symm⟩
  have hW : bitB (maskOf 256 (blockB (codeL 7 n2c))) (16 * j1 + j2) = true := by
    rw [bitB_maskOf _ _ _ (by omega)]
    unfold blockB
    rw [letB_eq, andB_iff, andB_iff, andB_iff, q3, q4, eu, ev,
      cand_num (by norm_num) lu (by norm_num) lv]
    have hV := validN_cand (a := 0) (b := 0) (by norm_num) lu (by norm_num) lv
    rw [fix6_codeL hV, fix6_codeL hV, fix6_codeL hV, fix6_codeL hV]
    have hS : ∀ y, y ∈ wL →
        mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand a u b v) y =
          mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand 0 u 0 v) y ∧
        mvN (CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over.cand 0 u 0 v) y ∈ wL :=
      cand_wL hu hv
    have k4 := rec_congr _ _ _ hS 6 4 (by decide)
    have k8 := rec_congr _ _ _ hS 6 8 (by decide)
    have k48 := rec_congr _ _ _ hS 6 48 (by decide)
    have k80 := rec_congr _ _ _ hS 6 80 (by decide)
    rw [rec6_of_relsOK hX hr (by norm_num)] at k4 k8 k48 k80
    exact ⟨k4.1.symm, k8.1.symm, k48.1.symm, k80.1.symm⟩
  have H := h3 (8 * i1 + i2) (by omega) hA (16 * j1 + j2) (by omega) hW
  rw [q1, q2, q3, q4, ea, eb, eu, ev, cand_num la lu lb lv] at H
  rcases H with H | H | H
  · exact absurd (relsK_of hR hX hr) H
  · exact Or.inl (codeL_inj hX validN_xSc H)
  · exact Or.inr (codeL_inj hX validN_xIc H)

end Pin

section KU

open CFSG.Quasithin.H13.MatNCert CFSG.KD.BfsK CFSG.KC.BfsK

@[expose] def MatHdr (R : ℕ → ℕ) : Prop :=
  (∀ i < 8, R i = codeL 6 ((sbGens ++ grs).getD i [])) ∧
  (∀ i < 8, R (8 + i) = codeL 6 ((sbInv ++ grsInv).getD i [])) ∧
  (∀ i < 3, R (58 + i) = codeL 6 (uGens.getD i []))

noncomputable instance (R : ℕ → ℕ) : Decidable (MatHdr R) := by unfold MatHdr; infer_instance

variable {n : ℕ}

theorem unit_of_inv {g gi : List ℕ} (hg : ValidN n g) (hgi : ValidN n gi)
    (h1 : mulN g gi = oneN n) (h2 : mulN gi g = oneN n) :
    ∃ u : GL (Fin n) (ZMod 2), (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g ∧
      ((u⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n gi :=
  ⟨⟨decN n g, decN n gi, by rw [← decN_mulN hg.1 hgi.1, h1, decN_oneN],
    by rw [← decN_mulN hgi.1 hg.1, h2, decN_oneN]⟩, rfl, rfl⟩

theorem card_of_tableKk {gens : List (List ℕ)} {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ}
    {o m k hiB hiS hiT : ℕ} (hk : gens.length = k) (hk0 : 0 < k) (hm : 0 < m)
    (hg : ∀ g ∈ gens, ValidN n g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g)
    (hst : ∀ y, ValidN n y → ∀ s < k, st (codeL n y) s = codeL n (mulN y (gens.getD s [])))
    (h0 : CFSG.KD.BfsK.recX R o 0 = codeL n (oneN n)) (h : tableKk R st o m k hiB hiS hiT = true)
    (hBm : m - 1 ≤ 64 * hiB) (hSm : m * k ≤ 64 * hiS) (hTm : m ≤ 64 * hiT) :
    Nat.card (genSubN n gens) = m := by
  have hinj : ∀ a b, validB n a = true → validB n b = true → codeL n a = codeL n b → a = b :=
    fun a b ha hb e => codeL_inj (validB_iff.1 ha) (validB_iff.1 hb) e
  have hst' : ∀ y N, Enc (validB n) (codeL n) y N → ∀ s < k, ∀ d : List ℕ,
      Enc (validB n) (codeL n) (colsN (decN n y * decN n (gens.getD s d))) (st N s) := by
    rintro y N ⟨hv, rfl⟩ s hs d
    have hyv := validB_iff.1 hv
    have hsl : s < gens.length := hk ▸ hs
    have e : gens.getD s d = gens.getD s [] := by
      rw [List.getD_eq_getElem _ _ hsl, List.getD_eq_getElem _ _ hsl]
    have hgv : ValidN n (gens.getD s []) := by
      rw [List.getD_eq_getElem _ _ hsl]
      exact hg _ (List.getElem_mem hsl)
    have em : colsN (decN n y * decN n (gens.getD s [])) = mulN y (gens.getD s []) := by
      rw [← decN_mulN hyv.1 hgv.1, colsN_decN (validN_mulN hyv hgv)]
    rw [e, em, hst y hyv s hs]
    exact ⟨validB_iff.2 (validN_mulN hyv hgv), rfl⟩
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validB n) (num := codeL n) hinj
    (start := oneN n) (mul := fun x y => colsN (decN n x * decN n y)) (gens := gens) (fuel := m)
    hk hk0 hm le_rfl hst' ⟨validB_iff.2 validN_oneN, h0.symm⟩ h hBm hSm hTm
  rw [← hsz]
  unfold genSubN
  refine CFSG.Quasithin.G2U.card_closure_eq (decN n) (oneN n) _ gens (Units.coeHom _)
    (fun _ _ e => Units.ext e)
    decN_oneN (fun x y => decN_colsN _) _ ?_ _ hcl hdi fun t ht t' ht' e => ?_
  · ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, decN_colsN _⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨u, hu⟩ := hunit c hc
      refine ⟨u, ?_, hu⟩
      change colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens
      rw [hu, colsN_decN (hg c hc)]
      exact hc
  · rw [hsz] at ht ht'
    exact decN_injOn (validB_iff.1 (hrec t ht).1) (validB_iff.1 (hrec t' ht').1) e

theorem kcK_eq : ∀ m < 64, kcK m = codeL 7 (kC m) := by decide +kernel

theorem validN_kC : ∀ m < 64, ValidN 7 (kC m) := by unfold ValidN; decide +kernel

theorem cntN_eq (f : ℕ → Bool) : ∀ m, cntN m f = ((List.range m).filter f).length
  | 0 => rfl
  | m + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (cntN m f) (Nat.succ (cntN m f)) (f m) = _
    rw [List.range_succ, List.filter_append, List.length_append, cntN_eq f m]
    cases hf : f m <;> simp [List.filter, hf]

theorem gen3_facts {x : List ℕ} (hx : ValidN 7 x) {j : ℕ} (hj : j < 3) :
    ValidN 7 ([nGc, nHc, x].getD j []) ∧
    ValidN 7 ([powN 7 nGc 6, powN 7 nHc 5, powN 7 x 5].getD j []) ∧
    [nGc, nHc, x].getD j [] ∈ [nGc, nHc, x] ∧
    gen3 (codeL 7 nGc) (codeL 7 nHc) (codeL 7 x) j = codeL 7 ([nGc, nHc, x].getD j []) ∧
    gen3 (codeL 7 (powN 7 nGc 6)) (codeL 7 (powN 7 nHc 5)) (codeL 7 (powN 7 x 5)) j =
      codeL 7 ([powN 7 nGc 6, powN 7 nHc 5, powN 7 x 5].getD j []) := by
  match j, hj with
  | 0, _ => exact ⟨validN_nGc, validN_powN' validN_nGc 6, by simp, rfl, rfl⟩
  | 1, _ => exact ⟨validN_nHc, validN_powN' validN_nHc 5, by simp, rfl, rfl⟩
  | 2, _ => exact ⟨hx, validN_powN' hx 5, by simp, rfl, rfl⟩

theorem case_facts {R : ℕ → ℕ} (hR : HdrOK R) (hP : PinHdr R) {x : List ℕ} (hx : ValidN 7 x)
    {kO kW rO : ℕ} (h : caseK R (codeL 7 x) kO kW rO 63 = true) :
    (∀ m, 0 < m → m < 64 → ∃ s ∈ genSubN 7 [nGc, nHc, x],
      decN 7 (kC m) = ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        decN 7 (kC 1) * ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) ∧
    ((List.range 128).filter fun v => mvN (bbarC x) v == v).length = 32 ∧
    (∀ g ∈ rGens x, mulN g (bbarC x) = mulN (bbarC x) g) ∧
    (∀ m ∈ [6, 8, 17, 33], mulN (kC m) (kC m) = oneN 7) ∧
    Nat.card (genSubN 7 (rGens x)) = 32 := by
  obtain ⟨-, -, -, -, -, hwd, -⟩ := hR
  obtain ⟨h17, h18, -, -⟩ := hP
  have hg3 : ∀ g ∈ [nGc, nHc, x], ValidN 7 g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl)
    exacts [validN_nGc, validN_nHc, hx]
  have hZv : ValidN 7 (bbarC x) := validN_evalW _ hg3 _
  have hPv : ValidN 7 (evalW 7 [nGc, nHc, x] wP1) := validN_evalW _ hg3 _
  have hword : ∀ i < 10, wordW (mulC 7) (codeL 7 (oneN 7))
      (gen3 (codeL 7 nGc) (codeL 7 nHc) (codeL 7 x)) (R (48 + i)) =
      codeL 7 (evalW 7 [nGc, nHc, x] (wordL.getD i [])) := by
    intro i hi
    obtain ⟨hl, hn⟩ := wordL_ok i hi
    rw [hwd i hi, wordW_encW _ _ _ hn]
    exact wordM_codeL (by norm_num) validN_nGc validN_nHc hx _ hl
  have eZ : wordW (mulC 7) (codeL 7 (oneN 7)) (gen3 (codeL 7 nGc) (codeL 7 nHc) (codeL 7 x))
      (R 49) = codeL 7 (bbarC x) := hword 1 (by norm_num)
  have eP : wordW (mulC 7) (codeL 7 (oneN 7)) (gen3 (codeL 7 nGc) (codeL 7 nHc) (codeL 7 x))
      (R 57) = codeL 7 (evalW 7 [nGc, nHc, x] wP1) := hword 9 (by norm_num)
  have eK1 := kcK_eq 1 (by norm_num)
  have eK6 := kcK_eq 6 (by norm_num)
  have eK8 := kcK_eq 8 (by norm_num)
  have eK17 := kcK_eq 17 (by norm_num)
  have eK33 := kcK_eq 33 (by norm_num)
  unfold caseK at h
  simp only [letB_eq, andB_iff, allN_iff, beq_iff, Nat.blt_eq, h17, h18, ONE7_eq,
    powM_codeL (by norm_num : 0 < 7) validN_nGc 6, powM_codeL (by norm_num : 0 < 7) validN_nHc 5,
    powM_codeL (by norm_num : 0 < 7) hx 5, eZ, eP, eK1, eK6, eK8, eK17, eK33] at h
  obtain ⟨hinv, h0, hbuild, hkw, hcnt, hcomm, hinvol, hr0, htab⟩ := h
  have hu3 : ∀ j < 3, ∃ u : GL (Fin 7) (ZMod 2),
      (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) = decN 7 ([nGc, nHc, x].getD j []) ∧
      ((u⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        decN 7 ([powN 7 nGc 6, powN 7 nHc 5, powN 7 x 5].getD j []) := by
    intro j hj
    obtain ⟨hg, hgi, -, e1, e2⟩ := gen3_facts hx hj
    obtain ⟨i1, i2⟩ := hinv j hj
    rw [e1, e2, ← codeL_mulN (by norm_num) hg hgi] at i1
    rw [e1, e2, ← codeL_mulN (by norm_num) hgi hg] at i2
    exact unit_of_inv hg hgi (codeL_inj (validN_mulN hg hgi) validN_oneN i1)
      (codeL_inj (validN_mulN hgi hg) validN_oneN i2)
  have hunit3 : ∀ g ∈ [nGc, nHc, x], ∃ u : GL (Fin 7) (ZMod 2),
      (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) = decN 7 g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← List.getD_eq_getElem _ [] hj]
    obtain ⟨u, hu, -⟩ := hu3 j hj
    exact ⟨u, hu⟩
  have hT : ∀ t, t < 63 → ∃ y, ValidN 7 y ∧ CFSG.KD.BfsK.recX R kO t = codeL 7 y ∧
      ∃ s ∈ genSubN 7 [nGc, nHc, x],
        decN 7 y = ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          decN 7 (kC 1) * ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      rcases t with _ | i
      · exact ⟨kC 1, validN_kC 1 (by norm_num), h0, 1, one_mem _, by simp⟩
      · obtain ⟨hpa, hpb, he⟩ := buildG_at hbuild (by norm_num) i (by omega)
        obtain ⟨y, hy, ey, s, hs, es⟩ := ih (CFSG.KD.BfsK.recF R kO 0 i) (by omega) (by omega)
        obtain ⟨hg, hgi, hmem, e1, e2⟩ := gen3_facts hx hpb
        obtain ⟨u, hu1, hu2⟩ := hu3 _ hpb
        refine ⟨_, validN_mulN (validN_mulN hg hy) hgi, ?_, u * s,
          mul_mem (Subgroup.subset_closure ?_) hs, ?_⟩
        · rw [he, ey]
          unfold CFSG.KD.Sp6Over.conjSt
          rw [e1, e2, ← codeL_mulN (by norm_num) hg hy,
            ← codeL_mulN (by norm_num) (validN_mulN hg hy) hgi]
        · change colsN (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) ∈ [nGc, nHc, x]
          rw [hu1, colsN_decN hg]
          exact hmem
        · rw [decN_mulN (validN_mulN hg hy).1 hgi.1, decN_mulN hg.1 hy.1, es, ← hu1, ← hu2,
            _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
          simp only [Matrix.mul_assoc]
  have hR5 : ∀ s < 5, ValidN 7 ((rGens x).getD s []) ∧
      gen5 (codeL 7 (kC 6)) (codeL 7 (kC 8)) (codeL 7 (kC 17)) (codeL 7 (kC 33))
        (codeL 7 (evalW 7 [nGc, nHc, x] wP1)) s = codeL 7 ((rGens x).getD s []) := by
    intro s hs
    match s, hs with
    | 0, _ => exact ⟨validN_kC 6 (by norm_num), rfl⟩
    | 1, _ => exact ⟨validN_kC 8 (by norm_num), rfl⟩
    | 2, _ => exact ⟨validN_kC 17 (by norm_num), rfl⟩
    | 3, _ => exact ⟨validN_kC 33 (by norm_num), rfl⟩
    | 4, _ => exact ⟨hPv, rfl⟩
  have hinv' : ∀ s < 4, mulN ((rGens x).getD s []) ((rGens x).getD s []) = oneN 7 := by
    intro s hs
    obtain ⟨hv, e5⟩ := hR5 s (by omega)
    have e := hinvol s hs
    rw [e5, ← codeL_mulN (by norm_num) hv hv] at e
    exact codeL_inj (validN_mulN hv hv) validN_oneN e
  have hrv : ∀ g ∈ rGens x, ValidN 7 g := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    rw [← List.getD_eq_getElem _ [] hs]
    exact (hR5 s hs).1
  refine ⟨fun m hm0 hm => ?_, ?_, fun g hg => ?_, fun m hm => ?_, ?_⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨hp, hpe⟩ := hkw m' (by omega)
    obtain ⟨y, hy, ey, s, hs, es⟩ := hT _ hp
    rw [hpe, kcK_eq _ (by omega)] at ey
    have e : kC (m' + 1) = y := codeL_inj (validN_kC _ (by omega)) hy ey
    rw [e]
    exact ⟨s, hs, es⟩
  · have hf : (fun v => mvN (bbarC x) v == v) =
        fun v => Nat.beq (mvC 7 (codeL 7 (bbarC x)) v) v := by
      funext v
      rw [mvC_codeL hZv]
      exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])
    rw [hf, ← cntN_eq]
    exact hcnt
  · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    rw [← List.getD_eq_getElem _ [] hs]
    obtain ⟨hv, e5⟩ := hR5 s hs
    have e := hcomm s hs
    rw [e5, ← codeL_mulN (by norm_num) hv hZv, ← codeL_mulN (by norm_num) hZv hv] at e
    exact codeL_inj (validN_mulN hv hZv) (validN_mulN hZv hv) e
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hinv' 0 (by norm_num)
    · exact hinv' 1 (by norm_num)
    · exact hinv' 2 (by norm_num)
    · exact hinv' 3 (by norm_num)
  · refine card_of_tableKk (k := 5) rfl (by norm_num) (by norm_num) hrv (fun g hg => ?_)
      (fun y hy s hs => ?_) hr0 htab (by norm_num) (by norm_num) (by norm_num)
    · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
      rw [← List.getD_eq_getElem _ [] hs]
      by_cases h4 : s < 4
      · obtain ⟨u, hu, -⟩ := unit_of_inv (hR5 s hs).1 (hR5 s hs).1 (hinv' s h4) (hinv' s h4)
        exact ⟨u, hu⟩
      · have hl : (rGens x).length = 5 := rfl
        obtain rfl : s = 4 := by omega
        obtain ⟨u, -, hu⟩ := exists_evalW _ hg3 hunit3 wP1
        exact ⟨u, hu⟩
    · obtain ⟨hv, e5⟩ := hR5 s hs
      rw [e5, codeL_mulN (by norm_num) hy hv]

theorem k_facts {R : ℕ → ℕ} (hR : HdrOK R) (hP : PinHdr R) (h : kK R 63 = true) {x : List ℕ}
    (hx : x = xSc ∨ x = xIc) :
    (∀ m, 0 < m → m < 64 → ∃ s ∈ genSubN 7 [nGc, nHc, x],
      decN 7 (kC m) = ((s : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        decN 7 (kC 1) * ((s⁻¹ : GL (Fin 7) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) ∧
    ((List.range 128).filter fun v => mvN (bbarC x) v == v).length = 32 ∧
    (∀ g ∈ rGens x, mulN g (bbarC x) = mulN (bbarC x) g) ∧
    (∀ m ∈ [6, 8, 17, 33], mulN (kC m) (kC m) = oneN 7) ∧
    Nat.card (genSubN 7 (rGens x)) = 32 := by
  unfold kK at h
  rw [andB_iff, letB_eq, letB_eq, hP.2.2.1, hP.2.2.2] at h
  rcases hx with rfl | rfl
  · exact case_facts hR hP validN_xSc h.1
  · exact case_facts hR hP validN_xIc h.2

theorem ONE_eq : ONE = codeL 6 (oneN 6) := by decide +kernel

theorem piK_xSc : piK (codeL 7 xSc) = codeL 6 (piC xSc) := by decide +kernel

theorem piK_xIc : piK (codeL 7 xIc) = codeL 6 (piC xIc) := by decide +kernel

theorem uGens_facts {s : ℕ} (hs : s < 3) : ValidN 6 (uGens.getD s []) ∧
    gen3 (codeL 6 (uGens.getD 0 [])) (codeL 6 (uGens.getD 1 [])) (codeL 6 (uGens.getD 2 [])) s =
      codeL 6 (uGens.getD s []) := by
  match s, hs with
  | 0, _ => exact ⟨by unfold ValidN; decide, rfl⟩
  | 1, _ => exact ⟨by unfold ValidN; decide, rfl⟩
  | 2, _ => exact ⟨by unfold ValidN; decide, rfl⟩

theorem u_facts {R : ℕ → ℕ} (hR : HdrOK R) (hP : PinHdr R) (hM : MatHdr R) (h : uK R = true) :
    piC xIc = piC xSc ∧ (∀ u ∈ uGens, mulN u u = oneN 6 ∧ mulN u pibbarC = mulN pibbarC u) ∧
    Nat.card (genSubN 6 uGens) = 32 := by
  obtain ⟨-, -, -, -, -, hwd, -⟩ := hR
  obtain ⟨-, -, h19, h20⟩ := hP
  obtain ⟨hm, -, hu⟩ := hM
  have e0 : R 0 = codeL 6 (piC nGc) := hm 0 (by norm_num)
  have e1 : R 1 = codeL 6 (piC nHc) := hm 1 (by norm_num)
  have e2 : R 2 = codeL 6 (piC xSc) := hm 2 (by norm_num)
  have eA : R 58 = codeL 6 (uGens.getD 0 []) := hu 0 (by norm_num)
  have eB : R 59 = codeL 6 (uGens.getD 1 []) := hu 1 (by norm_num)
  have eC : R 60 = codeL 6 (uGens.getD 2 []) := hu 2 (by norm_num)
  have v0 : ValidN 6 (piC nGc) := by unfold ValidN; decide
  have v1 : ValidN 6 (piC nHc) := by unfold ValidN; decide
  have v2 : ValidN 6 (piC xSc) := by unfold ValidN; decide
  have vI : ValidN 6 (piC xIc) := by unfold ValidN; decide
  have hZv : ValidN 6 pibbarC := validN_evalW _ (by
    simp only [sbGens, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl)
    exacts [v0, v1, v2]) _
  have eZ : wordW (mulC 6) (codeL 6 (oneN 6))
      (gen3 (codeL 6 (piC nGc)) (codeL 6 (piC nHc)) (codeL 6 (piC xSc))) (R 49) =
      codeL 6 pibbarC := by
    have hw : R 49 = encW wZ1 := hwd 1 (by norm_num)
    rw [hw, wordW_encW _ _ _ (by decide)]
    exact wordM_codeL (by norm_num) v0 v1 v2 wZ1 (by decide)
  unfold uK at h
  simp only [letB_eq, andB_iff, allN_iff, beq_iff, e0, e1, e2, eA, eB, eC, h19, h20, ONE_eq,
    eZ, piK_xSc, piK_xIc] at h
  obtain ⟨hpi, hgen, hr0, htab⟩ := h
  have hinv : ∀ s < 3, mulN (uGens.getD s []) (uGens.getD s []) = oneN 6 ∧
      mulN (uGens.getD s []) pibbarC = mulN pibbarC (uGens.getD s []) := by
    intro s hs
    obtain ⟨hv, e⟩ := uGens_facts hs
    obtain ⟨i1, i2⟩ := hgen s hs
    rw [e, ← codeL_mulN (by norm_num) hv hv] at i1
    rw [e, ← codeL_mulN (by norm_num) hv hZv, ← codeL_mulN (by norm_num) hZv hv] at i2
    exact ⟨codeL_inj (validN_mulN hv hv) validN_oneN i1,
      codeL_inj (validN_mulN hv hZv) (validN_mulN hZv hv) i2⟩
  have hmem : ∀ u ∈ uGens, ∃ s < 3, u = uGens.getD s [] := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hu
    exact ⟨s, hs, (List.getD_eq_getElem _ [] hs).symm⟩
  refine ⟨(codeL_inj v2 vI hpi).symm, fun u hu => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hmem u hu
    exact hinv s hs
  · refine card_of_tableKk (k := 3) rfl (by norm_num) (by norm_num)
      (fun g hg => ?_) (fun g hg => ?_) (fun y hy s hs => ?_) hr0 htab
      (by norm_num) (by norm_num) (by norm_num)
    · obtain ⟨s, hs, rfl⟩ := hmem g hg
      exact (uGens_facts hs).1
    · obtain ⟨s, hs, rfl⟩ := hmem g hg
      obtain ⟨u, hu, -⟩ := unit_of_inv (uGens_facts hs).1 (uGens_facts hs).1 (hinv s hs).1
        (hinv s hs).1
      exact ⟨u, hu⟩
    · obtain ⟨hv, e⟩ := uGens_facts hs
      rw [e, codeL_mulN (by norm_num) hy hv]

end KU

section Form

open CFSG.Quasithin.H13.MatNCert CFSG.KC.Misc.Spec
open CFSG.Quasithin.H13.Mat8Cert (b2z b2z_xor b2z_inj)
open CFSG.KC.Misc.G24 (oneF2)
open scoped Matrix

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] noncomputable def posAll : List ℕ := posL0 ++ posL1 ++ posL2

@[expose] noncomputable def pidx (i j : ℕ) : ℕ := posAll.idxOf (6 * i + j)

@[expose] noncomputable def decF (c : ℕ) : Mat6 :=
  Matrix.of fun i j => if (i : ℕ) < j then b2z (c.testBit (pidx i j))
    else if (j : ℕ) < i then b2z (c.testBit (pidx j i)) else 0

@[expose] noncomputable def basF (p : ℕ) : Mat6 := pkMat 6 (basQ (posAll.getD p 0))

@[expose] def FormHdr (R : ℕ → ℕ) : Prop := R 16 = sym15 (codeL 6 w0c)

noncomputable instance (R : ℕ → ℕ) : Decidable (FormHdr R) := by
  unfold FormHdr; infer_instance

theorem pidx_facts : ∀ i < 6, ∀ j < 6, i < j → pidx i j < 15 ∧
    posAll.getD (pidx i j) 0 = 6 * i + j := by decide

theorem pos_facts : ∀ p < 15, (posAll.getD p 0) / 6 < (posAll.getD p 0) % 6 ∧
    pidx ((posAll.getD p 0) / 6) ((posAll.getD p 0) % 6) = p := by decide

theorem decF_two_pow : ∀ p < 15, decF (2 ^ p) = basF p := by decide +kernel

theorem basF_alt : ∀ p < 15, (basF p)ᵀ = basF p ∧ ∀ i, basF p i i = 0 := by decide +kernel

theorem testBit_bitN (x q k : ℕ) : (bitN x q).testBit k = (decide (k = 0) && x.testBit q) := by
  rw [bitN_eq]
  cases x.testBit q <;> rcases k with _ | k <;> simp [Nat.testBit_zero, Nat.testBit_succ]

theorem testBit_symL (x : ℕ) : ∀ (l : List ℕ) (k : ℕ),
    (symL l x).testBit k = (decide (k < l.length) && x.testBit (l.getD k 0))
  | [], k => by simp [symL]
  | q :: l, k => by
    change (bitN x q ||| (symL l x <<< 1)).testBit k = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_bitN]
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel, testBit_symL x l k]
      simp

theorem testBit_sym15 (x p : ℕ) :
    (sym15 x).testBit p = (decide (p < 15) && x.testBit (posAll.getD p 0)) := by
  change (symL posL0 x ||| ((symL posL1 x <<< 5) ||| (symL posL2 x <<< 10))).testBit p = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_symL]
  by_cases hp : p < 15
  · interval_cases p <;> simp [posAll, posL0, posL1, posL2]
  · have h1 : ¬ p < 5 := by omega
    have h2 : ¬ p - 5 < 5 := by omega
    have h3 : ¬ p - 10 < 5 := by omega
    simp [posL0, posL1, posL2, hp, h1, h2, h3]

theorem sym15_lt (x : ℕ) : sym15 x < 2 ^ 15 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_sym15]
  simp
  omega

@[expose] def xs (f : ℕ → ℕ) (c n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun p acc => acc ^^^ (if c.testBit p then f p else 0)) n

theorem xs_succ (f : ℕ → ℕ) (c n : ℕ) :
    xs f c (n + 1) = xs f c n ^^^ (if c.testBit n then f n else 0) := rfl

theorem xs_lt {f : ℕ → ℕ} {k : ℕ} (c : ℕ) : ∀ n, (∀ p < n, f p < 2 ^ k) → xs f c n < 2 ^ k
  | 0, _ => Nat.two_pow_pos k
  | n + 1, h => by
    rw [xs_succ]
    refine Nat.xor_lt_two_pow (xs_lt c n fun p hp => h p (by omega)) ?_
    split_ifs
    · exact h n (by omega)
    · exact Nat.two_pow_pos k

theorem xs_congr (f : ℕ → ℕ) {c c' : ℕ} : ∀ n, (∀ p < n, c.testBit p = c'.testBit p) →
    xs f c n = xs f c' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [xs_succ, xs_succ, xs_congr f n fun p hp => h p (by omega), h n (by omega)]

theorem xs_zero (f : ℕ → ℕ) : ∀ n, xs f 0 n = 0
  | 0 => rfl
  | n + 1 => by rw [xs_succ, xs_zero f n]; simp

theorem testBit_xs_pow (c t : ℕ) : ∀ n,
    (xs (fun p => 2 ^ p) c n).testBit t = (decide (t < n) && c.testBit t)
  | 0 => by simp [xs]
  | n + 1 => by
    rw [xs_succ, Nat.testBit_xor, testBit_xs_pow c t n]
    by_cases ht : t < n
    · have : t ≠ n := by omega
      split_ifs <;> simp [Nat.testBit_two_pow, ht, this, Ne.symm this, show t < n + 1 by omega]
    · by_cases htn : t = n
      · subst htn
        split_ifs with h <;> simp [Nat.testBit_two_pow, h]
      · have : ¬ t < n + 1 := by omega
        split_ifs <;> simp [Nat.testBit_two_pow, ht, this, Ne.symm htn]

theorem xs_pow {c n : ℕ} (hc : c < 2 ^ n) : xs (fun p => 2 ^ p) c n = c := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_xs_pow]
  by_cases ht : t < n
  · simp [ht]
  · have h2 : 2 ^ n ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega)]
    simp [ht]

theorem decF_xor (a b : ℕ) : decF (a ^^^ b) = decF a + decF b := by
  ext i j
  simp only [decF, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor, b2z_xor]
  split_ifs <;> simp

theorem decF_zero : decF 0 = 0 := by
  ext i j
  simp only [decF, Matrix.of_apply, Nat.zero_testBit, Matrix.zero_apply]
  split_ifs <;> rfl

theorem decF_ite (p : Bool) (c : ℕ) : decF (if p then c else 0) = if p then decF c else 0 := by
  cases p
  · exact decF_zero
  · rfl

theorem decF_xs (f : ℕ → ℕ) (c : ℕ) : ∀ n,
    decF (xs f c n) = ∑ p ∈ Finset.range n, if c.testBit p then decF (f p) else 0
  | 0 => decF_zero
  | n + 1 => by rw [xs_succ, decF_xor, decF_xs f c n, decF_ite, Finset.sum_range_succ]

theorem decF_eq_sum {c : ℕ} (hc : c < 2 ^ 15) :
    decF c = ∑ p ∈ Finset.range 15, if c.testBit p then basF p else 0 := by
  conv_lhs => rw [← xs_pow hc]
  rw [decF_xs]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [decF_two_pow p (Finset.mem_range.mp hp)]

theorem decF_inj {a b : ℕ} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (h : decF a = decF b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 15
  · obtain ⟨hlt, hidx⟩ := pos_facts p hp
    have hj : posAll.getD p 0 % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have e := congrFun (congrFun h ⟨posAll.getD p 0 / 6, by omega⟩) ⟨posAll.getD p 0 % 6, hj⟩
    simp only [decF, Matrix.of_apply, if_pos hlt, hidx] at e
    exact b2z_inj e
  · have h2 : 2 ^ 15 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem decF_sym15 {x : ℕ} (hs : (pkMat 6 x)ᵀ = pkMat 6 x) (hd : ∀ i, pkMat 6 x i i = 0) :
    decF (sym15 x) = pkMat 6 x := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [decF, Matrix.of_apply]
  split_ifs with h1 h2
  · obtain ⟨hp, e⟩ := pidx_facts i hi j hj h1
    rw [testBit_sym15, e, decide_eq_true hp, Bool.true_and]
    rfl
  · obtain ⟨hp, e⟩ := pidx_facts j hj i hi h2
    rw [testBit_sym15, e, decide_eq_true hp, Bool.true_and, ← hs]
    rfl
  · have : i = j := Fin.ext (by omega)
    subst this
    exact (hd i).symm

theorem alt_conj (G B : Mat6) (hs : Bᵀ = B) (hd : ∀ i, B i i = 0) :
    (Gᵀ * B * G)ᵀ = Gᵀ * B * G ∧ ∀ i, (Gᵀ * B * G) i i = 0 := by
  set U : Mat6 := Matrix.of fun i j => if (i : ℕ) < j then B i j else 0
  have hB : B = U + Uᵀ := by
    ext i j
    simp only [U, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    by_cases h1 : (i : ℕ) < j
    · have : ¬ (j : ℕ) < i := by omega
      simp [h1, this]
    · by_cases h2 : (j : ℕ) < i
      · simp only [h1, h2, if_false, if_true, zero_add]
        exact (congrFun (congrFun hs i) j).symm
      · have : i = j := Fin.ext (by omega)
        subst this
        simp [hd i]
  have e : Gᵀ * B * G = Gᵀ * U * G + (Gᵀ * U * G)ᵀ := by
    rw [hB]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  refine ⟨?_, fun i => ?_⟩
  · rw [e, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  · rw [e, Matrix.add_apply, Matrix.transpose_apply]
    exact h2 _

theorem testBit_trCk (x p : ℕ) : ∀ k, (Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.lor acc
    (Nat.shiftLeft (bitN x t) (Nat.add (Nat.mul 6 (Nat.mod t 6)) (Nat.div t 6)))) k :
      ℕ).testBit p = true ↔ ∃ t < k, x.testBit t = true ∧ 6 * (t % 6) + t / 6 = p
  | 0 => by simp
  | k + 1 => by
    change (_ ||| (bitN x k <<< (6 * (k % 6) + k / 6))).testBit p = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_trCk x p k, Nat.testBit_shiftLeft,
      testBit_bitN]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, by omega, h⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨k, by omega, h.2.2, by omega⟩
    · rintro ⟨t, ht, h, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact Or.inl ⟨t, ht, h, e⟩
      · right
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by omega, h⟩

theorem pkMat_trC (x : ℕ) : pkMat 6 (trC 6 x) = (pkMat 6 x)ᵀ := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [pkMat, Matrix.of_apply, Matrix.transpose_apply]
  have key : (trC 6 x).testBit (6 * i + j) = x.testBit (6 * j + i) := by
    apply Bool.eq_iff_iff.mpr
    change (Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.lor acc
      (Nat.shiftLeft (bitN x t) (Nat.add (Nat.mul 6 (Nat.mod t 6)) (Nat.div t 6)))) 36 :
        ℕ).testBit _ = true ↔ _
    rw [testBit_trCk]
    constructor
    · rintro ⟨t, ht, h, e⟩
      have e1 : t % 6 = i := by omega
      have e2 : t / 6 = j := by omega
      rwa [show 6 * (j : ℕ) + i = t by omega]
    · intro h
      exact ⟨6 * j + i, by omega, h, by omega⟩
  rw [key]

theorem decF_imgF {g : List ℕ} (hg : ValidN 6 g) {p : ℕ} (hp : p < 15) :
    decF (imgF (codeL 6 g) (trC 6 (codeL 6 g)) (posAll.getD p 0)) =
      (decN 6 g)ᵀ * basF p * decN 6 g := by
  have hM : pkMat 6 (MULF (MULF (codeL 6 g) (basQ (posAll.getD p 0))) (trC 6 (codeL 6 g))) =
      (decN 6 g)ᵀ * basF p * decN 6 g := by
    rw [pkMat_MULF, pkMat_MULF, pkMat_trC, pkMat_codeL hg, Matrix.transpose_transpose]
    rfl
  obtain ⟨hs, hd⟩ := basF_alt p hp
  obtain ⟨hs', hd'⟩ := alt_conj (decN 6 g) _ hs hd
  unfold imgF
  rw [decF_sym15 (by rw [hM]; exact hs') (by rw [hM]; exact hd'), hM]

theorem xs_add (f : ℕ → ℕ) (c n : ℕ) : ∀ m,
    xs f c (n + m) = xs f c n ^^^ xs (fun p => f (n + p)) (c >>> n) m
  | 0 => by simp [xs]
  | m + 1 => by
    rw [← Nat.add_assoc, xs_succ, xs_add f c n m, xs_succ, Nat.testBit_shiftRight,
      Nat.xor_assoc]

@[expose] noncomputable def laneOK (T s P : ℕ) : Bool :=
  letB (trC 6 P) fun Q => allN 3 fun k => allN 32 fun v =>
    Nat.beq (lkT T (Nat.add (Nat.mul 3 s) k) v)
      (xs (fun p => imgF P Q (posAll.getD (5 * k + p) 0)) v 5)

theorem actT_eq {T s : ℕ} {g : List ℕ} (h : laneOK T s (codeL 6 g) = true) {c : ℕ}
    (hc : c < 2 ^ 15) :
    actT T s c = xs (fun p => imgF (codeL 6 g) (trC 6 (codeL 6 g)) (posAll.getD p 0)) c 15 := by
  unfold laneOK at h
  simp only [letB_eq, allN_iff, beq_iff] at h
  have h0 := h 0 (by norm_num) (Nat.land c 31) (Nat.and_lt_two_pow (n := 5) _ (by norm_num))
  have h1 := h 1 (by norm_num) (Nat.land (Nat.shiftRight c 5) 31)
    (Nat.and_lt_two_pow (n := 5) _ (by norm_num))
  have hc2 : Nat.shiftRight c 10 < 32 := by
    change c >>> 10 < 32
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 := h 2 (by norm_num) (Nat.shiftRight c 10) hc2
  have e0 : Nat.add (Nat.mul 3 s) 0 = Nat.mul 3 s := rfl
  rw [e0] at h0
  unfold actT
  rw [h0, h1, h2]
  change _ = xs _ c (5 + (5 + 5))
  rw [xs_add, xs_add]
  have m31 : (31 : ℕ) = 2 ^ 5 - 1 := rfl
  congr 1
  · refine xs_congr _ 5 fun p hp => ?_
    change (c &&& 31).testBit p = _
    rw [m31, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hp, Bool.and_true]
  congr 1
  · refine xs_congr _ 5 fun p hp => ?_
    change ((c >>> 5) &&& 31).testBit p = _
    rw [m31, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hp, Bool.and_true]

theorem decF_actT {T s : ℕ} {g : List ℕ} (hg : ValidN 6 g) (h : laneOK T s (codeL 6 g) = true)
    {c : ℕ} (hc : c < 2 ^ 15) :
    decF (actT T s c) = (decN 6 g)ᵀ * decF c * decN 6 g ∧ actT T s c < 2 ^ 15 := by
  rw [actT_eq h hc]
  refine ⟨?_, xs_lt c 15 fun p hp => by unfold imgF; exact sym15_lt _⟩
  rw [decF_xs, decF_eq_sum hc, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [decF_imgF hg (Finset.mem_range.mp hp)]
  split_ifs <;> simp

theorem actT_lt (T s c : ℕ) : actT T s c < 2 ^ 16 := by
  have h : ∀ x, Nat.land x 65535 < 2 ^ 16 := fun x => Nat.and_lt_two_pow x (by norm_num)
  unfold actT lkT
  exact Nat.xor_lt_two_pow (h _) (Nat.xor_lt_two_pow (h _) (h _))

theorem codeL_append (n : ℕ) : ∀ A B : List ℕ,
    codeL n (A ++ B) = codeL n A + 2 ^ (n * A.length) * codeL n B
  | [], B => by simp [codeL]
  | c :: A, B => by
    change c + 2 ^ n * codeL n (A ++ B) =
      c + 2 ^ n * codeL n A + 2 ^ (n * (A.length + 1)) * codeL n B
    rw [codeL_append n A B, Nat.mul_succ, Nat.pow_add]
    ring

theorem codeL_append_or {n : ℕ} {A : List ℕ} (hA : ∀ c ∈ A, c < 2 ^ n) (B : List ℕ) :
    codeL n (A ++ B) = codeL n A ||| (codeL n B <<< (n * A.length)) := by
  rw [codeL_append, add_pow_mul_eq_or (codeL_lt hA)]

theorem lk16_rootsOf (R : ℕ → ℕ) {W0 : ℕ} (hW : W0 < 2 ^ 16) :
    lk16 (rootsOf R W0) 0 = W0 ∧
      ∀ r < 5, lk16 (rootsOf R W0) (r + 1) = actT (tabs (R (3 + r))) 0 W0 := by
  set a : ℕ → ℕ := fun r => actT (tabs (R (Nat.add 3 r))) 0 W0
  have ha : ∀ r, a r < 2 ^ 16 := fun r => actT_lt _ _ _
  have key : ∀ k, Nat.rec (motive := fun _ => ℕ) W0 (fun r acc => Nat.lor acc
      (Nat.shiftLeft (a r) (Nat.mul 16 (Nat.succ r)))) k =
        codeL 16 (W0 :: (List.range k).map a) := by
    intro k
    induction k with
    | zero => simp [codeL]
    | succ k ih =>
      have hL : ∀ c ∈ W0 :: (List.range k).map a, c < 2 ^ 16 := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hW
        · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hc
          exact ha r
      change Nat.rec (motive := fun _ => ℕ) W0 (fun r acc => Nat.lor acc
        (Nat.shiftLeft (a r) (Nat.mul 16 (Nat.succ r)))) k ||| (a k <<< (16 * (k + 1))) = _
      rw [ih, List.range_succ, List.map_append, ← List.cons_append, codeL_append_or hL]
      simp [codeL]
  have hall : ∀ c ∈ W0 :: (List.range 5).map a, c < 2 ^ 16 := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hW
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hc
      exact ha r
  have e : ∀ i, lk16 (rootsOf R W0) i = (W0 :: (List.range 5).map a).getD i 0 := by
    intro i
    rw [← colC_codeL hall i, ← key 5]
    rfl
  refine ⟨by rw [e]; rfl, fun r hr => ?_⟩
  rw [e, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
    List.getElem_range]
  rfl

@[expose] def stepT (TAB a b : ℕ) : Prop := ∃ s < 3, b = actT TAB s a

theorem wk6_bIf (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem testBit_lk16 (x j i : ℕ) :
    (lk16 x j).testBit i = (decide (i < 16) && x.testBit (16 * j + i)) := by
  have e : lk16 x j = (x >>> (16 * j)) &&& (2 ^ 16 - 1) := rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem wk6_testBit_hi {c : ℕ} (hc : c < 2 ^ 16) {i : ℕ} (hi : 16 ≤ i) : c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))

theorem lk16_zero (j : ℕ) : lk16 0 j = 0 :=
  Nat.eq_of_testBit_eq fun i => by rw [testBit_lk16, Nat.zero_testBit, Nat.zero_testBit, Bool.and_false]

theorem lk16_small {c : ℕ} (hc : c < 2 ^ 16) (j : ℕ) : lk16 c j = c ∨ lk16 c j = 0 := by
  rcases j with _ | j
  · left
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_lk16]
    by_cases hi : i < 16
    · simp [hi]
    · simp [hi, wk6_testBit_hi hc (by omega : 16 ≤ i)]
  · right
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_lk16, Nat.zero_testBit, wk6_testBit_hi hc (by omega : 16 ≤ 16 * (j + 1) + i),
      Bool.and_false]

theorem lk16_upd {path c d : ℕ} (hc : c < 2 ^ 16) (j : ℕ) :
    lk16 (Nat.lor (Nat.land path (mskN (Nat.mul 16 d))) (Nat.shiftLeft c (Nat.mul 16 d))) j =
        lk16 path j ∨
      lk16 (Nat.lor (Nat.land path (mskN (Nat.mul 16 d))) (Nat.shiftLeft c (Nat.mul 16 d))) j = c ∨
      lk16 (Nat.lor (Nat.land path (mskN (Nat.mul 16 d))) (Nat.shiftLeft c (Nat.mul 16 d))) j = 0 := by
  have tp : ∀ k, (Nat.lor (Nat.land path (mskN (Nat.mul 16 d)))
      (Nat.shiftLeft c (Nat.mul 16 d))).testBit k =
        ((path.testBit k && decide (k < 16 * d)) ||
          (decide (k ≥ 16 * d) && c.testBit (k - 16 * d))) := by
    intro k
    have e : Nat.lor (Nat.land path (mskN (Nat.mul 16 d))) (Nat.shiftLeft c (Nat.mul 16 d)) =
        (path &&& (2 ^ (16 * d) - 1)) ||| (c <<< (16 * d)) := by
      rw [← mskN_eq]; rfl
    rw [e, Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  rcases lt_trichotomy j d with hj | rfl | hj
  · left
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_lk16, testBit_lk16, tp]
    by_cases hi : i < 16
    · have h1 : 16 * j + i < 16 * d := by omega
      have h2 : ¬ 16 * j + i ≥ 16 * d := by omega
      simp [hi, h1, h2]
    · simp [hi]
  · right; left
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_lk16, tp]
    by_cases hi : i < 16
    · have h1 : ¬ 16 * j + i < 16 * j := by omega
      simp [hi, h1]
    · simp [hi, wk6_testBit_hi hc (by omega : 16 ≤ i)]
  · right; right
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_lk16, tp, Nat.zero_testBit]
    by_cases hi : i < 16
    · have h1 : ¬ 16 * j + i < 16 * d := by omega
      have h2 : 16 * j + i ≥ 16 * d := by omega
      simp [hi, h1, h2, wk6_testBit_hi hc (by omega : 16 ≤ 16 * j + i - 16 * d)]
    · simp [hi]

theorem wk6_bits_lo {n S : ℕ} (hn : n < 2 ^ 64) : Nat.land (n + 2 ^ 64 * S) M64 = n :=
  land_low 64 hn

theorem wk6_bits_test {n S c : ℕ} (hn : n < 2 ^ 64)
    (h : Nat.land (n + 2 ^ 64 * S) (Nat.shiftLeft 1 (Nat.add c 64)) = 0) : S.testBit c = false := by
  have e1 : (n + 2 ^ 64 * S).testBit (64 + c) = S.testBit c := by
    rw [← Nat.testBit_shiftRight]
    exact congrArg (Nat.testBit · c) (shr_high 64 hn)
  have e2 := congrArg (Nat.testBit · (64 + c)) h
  change ((n + 2 ^ 64 * S) &&& (1 <<< (c + 64))).testBit (64 + c) = (0 : ℕ).testBit (64 + c) at e2
  rw [Nat.add_comm c 64, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self,
    Bool.and_true, Nat.zero_testBit] at e2
  rw [← e1, e2]

theorem wk6_bits_add {n S c : ℕ} (hn : n + 1 < 2 ^ 64) :
    Nat.add (Nat.lor (n + 2 ^ 64 * S) (Nat.shiftLeft 1 (Nat.add c 64))) 1 =
      (n + 1) + 2 ^ 64 * (S ||| 2 ^ c) := by
  have hn' : n < 2 ^ 64 := by omega
  have h : Nat.lor (n + 2 ^ 64 * S) (Nat.shiftLeft 1 (Nat.add c 64)) =
      n + 2 ^ 64 * (S ||| 2 ^ c) := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    change ((n + 2 ^ 64 * S) ||| (1 <<< (c + 64))).testBit i = _
    rw [Nat.one_shiftLeft, add_pow_mul_eq_or hn', add_pow_mul_eq_or hn', Nat.testBit_or,
      Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
    by_cases hi : 64 ≤ i
    · have e : (c + 64 = i) ↔ (c = i - 64) := by omega
      simp [hi, e, Bool.or_assoc]
    · have e : c + 64 ≠ i := by omega
      simp [hi, e]
  rw [h]
  change n + 2 ^ 64 * (S ||| 2 ^ c) + 1 = _
  omega

def WalkInv (TAB ROOTS ST m path bits rc : ℕ) : Prop :=
  ∃ T : ℕ → List ℕ, ∃ n S : ℕ, bits = n + 2 ^ 64 * S ∧ n ≤ m ∧
    (∀ x, S.testBit x = true ↔ ∃ r, x ∈ T r) ∧ (∀ r, (T r).Nodup) ∧
    (∀ r r' x, x ∈ T r → x ∈ T r' → r = r') ∧ (∀ r, rc ≤ r → T r = []) ∧
    (∀ r, r + 1 < rc → (T r).length + lk16 ST r = lk16 ST (r + 1)) ∧
    (∀ k, rc = k + 1 → n = lk16 ST k + (T k).length) ∧
    (∀ r < rc, ∀ c ∈ T r, Relation.ReflTransGen (stepT TAB) (lk16 ROOTS r) c) ∧
    ∀ j, lk16 path j = 0 ∨
      ∃ k, rc = k + 1 ∧ Relation.ReflTransGen (stepT TAB) (lk16 ROOTS k) (lk16 path j)

theorem WalkInv.ins {TAB ROOTS ST m : ℕ} {T : ℕ → List ℕ} {n S : ℕ} (hm : m + 1 < 2 ^ 64)
    (hn : n ≤ m) (hS : ∀ x, S.testBit x = true ↔ ∃ r, x ∈ T r) (hnd : ∀ r, (T r).Nodup)
    (hdj : ∀ r r' x, x ∈ T r → x ∈ T r' → r = r') {c k rc p : ℕ}
    (hbit : Nat.land (n + 2 ^ 64 * S) (Nat.shiftLeft 1 (Nat.add c 64)) = 0)
    (hc : Relation.ReflTransGen (stepT TAB) (lk16 ROOTS k) c) (hk : rc = k + 1)
    (hemp : ∀ r, rc ≤ r → T r = [])
    (hlen : ∀ r, r + 1 < rc → (T r).length + lk16 ST r = lk16 ST (r + 1))
    (hcur : n = lk16 ST k + (T k).length)
    (hreach : ∀ r < rc, ∀ x ∈ T r, Relation.ReflTransGen (stepT TAB) (lk16 ROOTS r) x)
    (hpath : ∀ j, lk16 p j = 0 ∨
      ∃ k, rc = k + 1 ∧ Relation.ReflTransGen (stepT TAB) (lk16 ROOTS k) (lk16 p j)) :
    WalkInv TAB ROOTS ST (m + 1) p
      (Nat.add (Nat.lor (n + 2 ^ 64 * S) (Nat.shiftLeft 1 (Nat.add c 64))) 1) rc := by
  have hcS : ∀ r, c ∉ T r := fun r hr => by
    have := (hS c).2 ⟨r, hr⟩
    rw [wk6_bits_test (by omega) hbit] at this
    exact Bool.false_ne_true this
  have hmem : ∀ r x, x ∈ (if r = k then c :: T r else T r) ↔ (r = k ∧ x = c) ∨ x ∈ T r := by
    intro r x
    split_ifs with h <;> simp [h]
  refine ⟨fun r => if r = k then c :: T r else T r, n + 1, S ||| 2 ^ c, wk6_bits_add (by omega),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpath⟩
  · intro x
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hS, decide_eq_true_iff]
    constructor
    · rintro (⟨r, hr⟩ | rfl)
      · exact ⟨r, (hmem r x).2 (Or.inr hr)⟩
      · exact ⟨k, (hmem k c).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · rintro ⟨r, hr⟩
      rcases (hmem r x).1 hr with ⟨-, rfl⟩ | hr
      · exact Or.inr rfl
      · exact Or.inl ⟨r, hr⟩
  · intro r
    dsimp only
    split_ifs
    · exact List.nodup_cons.2 ⟨hcS r, hnd r⟩
    · exact hnd r
  · intro r r' x hr hr'
    rcases (hmem r x).1 hr with ⟨hrk, rfl⟩ | hx1
    · rcases (hmem r' x).1 hr' with ⟨hrk', -⟩ | hx2
      · rw [hrk, hrk']
      · exact absurd hx2 (hcS r')
    · rcases (hmem r' x).1 hr' with ⟨-, rfl⟩ | hx2
      · exact absurd hx1 (hcS r)
      · exact hdj r r' x hx1 hx2
  · intro r hr
    dsimp only
    rw [if_neg (by omega)]
    exact hemp r hr
  · intro r hr
    dsimp only
    rw [if_neg (by omega)]
    exact hlen r hr
  · intro k' hk'
    obtain rfl : k' = k := by omega
    dsimp only
    rw [if_pos rfl, List.length_cons]
    omega
  · intro r hr x hx
    rcases (hmem r x).1 hx with ⟨rfl, rfl⟩ | hx
    · exact hc
    · exact hreach r hr x hx

theorem WalkInv.step {TAB ROOTS ST m r path bits rc : ℕ} {K : ℕ → ℕ → ℕ → Bool}
    (h0 : ∀ s < 3, actT TAB s 0 = 0) (hm : m + 1 < 2 ^ 64)
    (hI : WalkInv TAB ROOTS ST m path bits rc)
    (h : walkStep TAB ROOTS ST r path bits rc K = true) :
    ∃ p b c, WalkInv TAB ROOTS ST (m + 1) p b c ∧ K p b c = true := by
  obtain ⟨T, n, S, rfl, hn, hS, hnd, hdj, hemp, hlen, hcur, hreach, hpath⟩ := hI
  unfold walkStep at h
  simp only [letB_eq] at h
  rw [wk6_bIf] at h
  split_ifs at h with hd
  · simp only [andB_iff, blt_iff, beq_iff] at h
    obtain ⟨hrc, hst, hadd⟩ := h
    unfold addC at hadd
    simp only [andB_iff, letB_eq, blt_iff, beq_iff] at hadd
    obtain ⟨-, hbit, hK⟩ := hadd
    rw [wk6_bits_lo (by omega)] at hst
    have hlt : lk16 ROOTS rc < 2 ^ 16 := Nat.and_lt_two_pow _ (by norm_num)
    refine ⟨_, _, _, WalkInv.ins hm hn hS hnd hdj hbit .refl rfl
      (fun r hr => hemp r (by omega)) ?_ (by rw [hemp rc le_rfl]; simpa using hst) ?_ ?_, hK⟩
    · intro r hr
      rcases Nat.lt_or_ge (r + 1) rc with h' | h'
      · exact hlen r h'
      · obtain rfl : rc = r + 1 := by omega
        have := hcur r rfl
        omega
    · intro r hr x hx
      rcases Nat.lt_or_ge r rc with h' | h'
      · exact hreach r h' x hx
      · rw [hemp r h'] at hx
        exact absurd hx (List.not_mem_nil)
    · intro j
      rcases lk16_small hlt j with e | e
      · exact Or.inr ⟨rc, rfl, by rw [e]⟩
      · exact Or.inl e
  · simp only [andB_iff, blt_iff] at h
    obtain ⟨hs, hadd⟩ := h
    unfold addC at hadd
    simp only [andB_iff, letB_eq, blt_iff, beq_iff] at hadd
    obtain ⟨hc0, hbit, hK⟩ := hadd
    rcases hpath (Nat.pred (Nat.land r 63)) with hz | ⟨k, hk, hr⟩
    · rw [hz, h0 _ hs] at hc0
      exact absurd hc0 (lt_irrefl 0)
    · have hrc : Relation.ReflTransGen (stepT TAB) (lk16 ROOTS k)
          (actT TAB (Nat.shiftRight r 6) (lk16 path (Nat.pred (Nat.land r 63)))) :=
        hr.tail ⟨_, hs, rfl⟩
      refine ⟨_, _, _, WalkInv.ins hm hn hS hnd hdj hbit hrc hk hemp hlen (hcur k hk) hreach ?_,
        hK⟩
      intro j
      rcases lk16_upd (path := path) (d := Nat.land r 63) (actT_lt _ _ _) j with e | e | e
      · rw [e]
        exact hpath j
      · rw [e]
        exact Or.inr ⟨k, hk, hrc⟩
      · exact Or.inl e

theorem WalkInv.chunk {TAB ROOTS ST : ℕ} {K : ℕ → ℕ → ℕ → Bool}
    (h0 : ∀ s < 3, actT TAB s 0 = 0) :
    ∀ k ch m path bits rc, m + k < 2 ^ 64 → WalkInv TAB ROOTS ST m path bits rc →
      Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun _ path bits rc => K path bits rc)
        (fun _ ih ch path bits rc => walkStep TAB ROOTS ST (Nat.land ch 255) path bits rc
          (fun p b c => ih (Nat.shiftRight ch 8) p b c)) k ch path bits rc = true →
      ∃ p b c, WalkInv TAB ROOTS ST (m + k) p b c ∧ K p b c = true := by
  intro k
  induction k with
  | zero => exact fun ch m path bits rc _ hI h => ⟨path, bits, rc, hI, h⟩
  | succ k ih =>
    intro ch m path bits rc hm hI h
    obtain ⟨p, b, c, hI', hK⟩ := WalkInv.step h0 (by omega) hI h
    obtain ⟨p', b', c', hI'', hK'⟩ := ih _ _ _ _ _ (by omega) hI' hK
    refine ⟨p', b', c', ?_, hK'⟩
    rwa [show m + (k + 1) = m + 1 + k by omega]

theorem WalkInv.all {TAB ROOTS ST : ℕ} {K : ℕ → ℕ → ℕ → Bool}
    (h0 : ∀ s < 3, actT TAB s 0 = 0) :
    ∀ (F : List ℕ) m path bits rc, m + 64 * F.length < 2 ^ 64 →
      WalkInv TAB ROOTS ST m path bits rc → walkAll TAB ROOTS ST F K path bits rc = true →
      ∃ m' p b c, m' < 2 ^ 64 ∧ WalkInv TAB ROOTS ST m' p b c ∧ K p b c = true
  | [], m, path, bits, rc, hm, hI, h => ⟨m, path, bits, rc, by simpa using hm, hI, h⟩
  | ch :: F, m, path, bits, rc, hm, hI, h => by
    simp only [List.length_cons] at hm
    obtain ⟨p, b, c, hI', hK⟩ := WalkInv.chunk (K := walkAll TAB ROOTS ST F K) h0 64 ch m path
      bits rc (by omega) hI h
    exact WalkInv.all h0 F (m + 64) p b c (by omega) hI' hK

theorem WalkInv.init (TAB ROOTS ST : ℕ) : WalkInv TAB ROOTS ST 0 0 0 0 :=
  ⟨fun _ => [], 0, 0, by norm_num, le_rfl, by simp, fun _ => List.nodup_nil, by simp,
    fun _ _ => rfl, fun r hr => absurd hr (by omega), fun k hk => absurd hk (by omega),
    fun r hr => absurd hr (by omega), fun j => Or.inl (lk16_zero j)⟩

theorem walk_sound {TAB ROOTS ST : ℕ} {F : List ℕ} (h0 : ∀ s < 3, actT TAB s 0 = 0)
    (hF : 64 * F.length < 2 ^ 64)
    (h : walkAll TAB ROOTS ST F (fun _ bits rc =>
      andB (Nat.beq rc 6) (Nat.beq (Nat.land bits M64) (lk16 ST 6))) 0 0 0 = true) :
    ∃ T : ℕ → List ℕ, (∀ r < 6, (T r).length + lk16 ST r = lk16 ST (r + 1)) ∧
      ((List.range 6).flatMap T).Nodup ∧
      ∀ r < 6, ∀ c ∈ T r, Relation.ReflTransGen (stepT TAB) (lk16 ROOTS r) c := by
  obtain ⟨m, p, b, c, hm, ⟨T, n, S, rfl, hn, -, hnd, hdj, -, hlen, hcur, hreach, -⟩, hK⟩ :=
    WalkInv.all h0 F 0 0 0 0 (by omega) (WalkInv.init TAB ROOTS ST) h
  simp only [andB_iff, beq_iff] at hK
  obtain ⟨rfl, hst⟩ := hK
  rw [wk6_bits_lo (by omega)] at hst
  refine ⟨T, fun r hr => ?_, ?_, hreach⟩
  · rcases Nat.lt_or_ge (r + 1) 6 with h' | h'
    · exact hlen r h'
    · obtain rfl : r = 5 := by omega
      have := hcur 5 rfl
      change (T 5).length + lk16 ST 5 = lk16 ST 6
      omega
  · rw [List.nodup_flatMap]
    exact ⟨fun r _ => hnd r, List.Pairwise.imp (fun {a b} hab x hxa hxb => hab (hdj a b x hxa hxb))
      List.nodup_range⟩

theorem reach_inv {TAB a c : ℕ} {P : ℕ → Prop} (hs : ∀ s < 3, ∀ x, P x → P (actT TAB s x))
    (ha : P a) (h : Relation.ReflTransGen (stepT TAB) a c) : P c := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨s, hs3, rfl⟩ := hbc
    exact hs s hs3 _ ih

@[expose] noncomputable def tabAll (R : ℕ → ℕ) : ℕ :=
  Nat.lor (tabs (R 0)) (Nat.lor (Nat.shiftLeft (tabs (R 1)) 1536) (Nat.shiftLeft (tabs (R 2)) 3072))

theorem oneF2_eq : oneF2 6 = codeL 6 (oneN 6) := by decide +kernel

theorem mats_valid : ∀ i < 8, ValidN 6 ((sbGens ++ grs).getD i []) ∧
    ValidN 6 ((sbInv ++ grsInv).getD i []) := by
  unfold ValidN; decide +kernel

theorem getD_mats : (∀ s < 3, (sbGens ++ grs).getD s [] = sbGens.getD s []) ∧
    ∀ r < 5, (sbGens ++ grs).getD (3 + r) [] = grs.getD r [] := by decide +kernel

theorem decF_w0c : decF (sym15 (codeL 6 w0c)) = decN 6 w0c := by decide +kernel

theorem form_facts {R : ℕ → ℕ} (hM : MatHdr R) (hW : FormHdr R) {F : List ℕ} {ST : ℕ}
    (hF : 64 * F.length < 2 ^ 64)
    (hST : ∀ r < 6, lk16 ST (r + 1) - lk16 ST r = [1, 315, 2880, 2880, 3780, 4032].getD r 0)
    (hL : ∀ s < 3, laneOK (tabAll R) s (R s) = true)
    (hL' : ∀ r < 5, laneOK (tabs (R (3 + r))) 0 (R (3 + r)) = true)
    (h : formK R F ST = true) :
    (∀ g ∈ sbGens, (decN 6 g)ᵀ * decN 6 w0c * decN 6 g = decN 6 w0c) ∧
    (∀ g ∈ sbGens ++ grs, ∃ u : GL (Fin 6) (ZMod 2), (u : Mat6) = decN 6 g) ∧
    ∃ T : ℕ → List Mat6, T 0 = [decN 6 w0c] ∧
      (∀ r < 5, (T (r + 1)).length = [315, 2880, 2880, 3780, 4032].getD r 0) ∧
      ((List.range 6).flatMap T).Nodup ∧
      ∀ r < 5, ∀ x ∈ T (r + 1), ∃ u : GL (Fin 6) (ZMod 2),
        (u : Mat6) = decN 6 (grs.getD r []) ∧ ∃ s ∈ genSubN 6 sbGens,
          x = ((u * s : GL (Fin 6) (ZMod 2)) : Mat6)ᵀ * decN 6 w0c *
            ((u * s : GL (Fin 6) (ZMod 2)) : Mat6) := by
  obtain ⟨hm, hi, -⟩ := hM
  have hv : ∀ m < 8, ValidN 6 ((sbGens ++ grs).getD m []) := fun m hm8 => (mats_valid m hm8).1
  have hvi : ∀ m < 8, ValidN 6 ((sbInv ++ grsInv).getD m []) := fun m hm8 =>
    (mats_valid m hm8).2
  have hW0 : decF (R 16) = decN 6 w0c := by rw [hW, decF_w0c]
  have hW15 : R 16 < 2 ^ 15 := by rw [hW]; exact sym15_lt _
  unfold formK at h
  simp only [letB_eq, andB_iff, allN_iff, beq_iff] at h
  obtain ⟨hfix, hinv, hw⟩ := h
  have hunit : ∀ m < 8, ∃ u : GL (Fin 6) (ZMod 2),
      (u : Mat6) = decN 6 ((sbGens ++ grs).getD m []) := by
    intro m hm8
    have e1 : mulC 6 (R m) (R (8 + m)) = oneF2 6 := (hinv m hm8).1
    have e2 : mulC 6 (R (8 + m)) (R m) = oneF2 6 := (hinv m hm8).2
    rw [hm m hm8, hi m hm8, ← codeL_mulN (by norm_num) (hv m hm8) (hvi m hm8), oneF2_eq] at e1
    rw [hm m hm8, hi m hm8, ← codeL_mulN (by norm_num) (hvi m hm8) (hv m hm8), oneF2_eq] at e2
    obtain ⟨u, hu, -⟩ := unit_of_inv (hv m hm8) (hvi m hm8)
      (codeL_inj (validN_mulN (hv m hm8) (hvi m hm8)) validN_oneN e1)
      (codeL_inj (validN_mulN (hvi m hm8) (hv m hm8)) validN_oneN e2)
    exact ⟨u, hu⟩
  have hvS : ∀ s < 3, ValidN 6 (sbGens.getD s []) := fun s hs => by
    rw [← getD_mats.1 s hs]; exact hv s (by omega)
  have hvG : ∀ r < 5, ValidN 6 (grs.getD r []) := fun r hr => by
    rw [← getD_mats.2 r hr]; exact hv (3 + r) (by omega)
  have hmemS : ∀ g ∈ sbGens, ∃ s < 3, g = sbGens.getD s [] := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg
    exact ⟨s, hs, (List.getD_eq_getElem _ [] hs).symm⟩
  have hvSall : ∀ g ∈ sbGens, ValidN 6 g := fun g hg => by
    obtain ⟨s, hs, rfl⟩ := hmemS g hg
    exact hvS s hs
  have huS : ∀ s < 3, ∃ v ∈ genSubN 6 sbGens, (v : Mat6) = decN 6 (sbGens.getD s []) := by
    intro s hs
    obtain ⟨v, hv'⟩ := hunit s (by omega)
    rw [getD_mats.1 s hs] at hv'
    have hsl : s < sbGens.length := hs
    have hmem : sbGens.getD s [] ∈ sbGens := by
      rw [List.getD_eq_getElem _ _ hsl]
      exact List.getElem_mem hsl
    exact ⟨v, mem_genSubN_of_mem hvSall hmem hv', hv'⟩
  have hact : ∀ s < 3, ∀ c < 2 ^ 15, decF (actT (tabAll R) s c) =
      (decN 6 (sbGens.getD s []))ᵀ * decF c * decN 6 (sbGens.getD s []) ∧
        actT (tabAll R) s c < 2 ^ 15 := by
    intro s hs c hc
    have hl := hL s hs
    rw [hm s (by omega), getD_mats.1 s hs] at hl
    exact decF_actT (hvS s hs) hl hc
  have hfix' : ∀ s < 3, (decN 6 (sbGens.getD s []))ᵀ * decN 6 w0c * decN 6 (sbGens.getD s []) =
      decN 6 w0c := by
    intro s hs
    have e := (hact s hs _ hW15).1
    have hf : actT (tabAll R) s (R 16) = R 16 := hfix s hs
    rw [hf, hW0] at e
    exact e.symm
  have h0 : ∀ s < 3, actT (tabAll R) s 0 = 0 := by
    intro s hs
    have hl := hL s hs
    rw [hm s (by omega), getD_mats.1 s hs] at hl
    rw [actT_eq hl (Nat.two_pow_pos 15), xs_zero]
  have hw' : walkAll (tabAll R) (rootsOf R (R 16)) ST F (fun _ bits rc =>
      andB (Nat.beq rc 6) (Nat.beq (Nat.land bits M64) (lk16 ST 6))) 0 0 0 = true := hw
  obtain ⟨T, hlen, hnd, hreach⟩ := walk_sound h0 hF hw'
  obtain ⟨hr0, hrs⟩ := lk16_rootsOf R (W0 := R 16) (by omega)
  have inv0 : ∀ c ∈ T 0, c < 2 ^ 15 ∧ decF c = decN 6 w0c := by
    intro c hc
    have h' := hreach 0 (by norm_num) c hc
    rw [hr0] at h'
    refine reach_inv (P := fun x => x < 2 ^ 15 ∧ decF x = decN 6 w0c)
      (fun s hs x hx => ?_) ⟨hW15, hW0⟩ h'
    obtain ⟨e, hlt⟩ := hact s hs x hx.1
    exact ⟨hlt, by rw [e, hx.2, hfix' s hs]⟩
  have invr : ∀ r < 5, ∃ u : GL (Fin 6) (ZMod 2), (u : Mat6) = decN 6 (grs.getD r []) ∧
      ∀ c ∈ T (r + 1), c < 2 ^ 15 ∧ ∃ s ∈ genSubN 6 sbGens,
        decF c = ((u * s : GL (Fin 6) (ZMod 2)) : Mat6)ᵀ * decN 6 w0c *
          ((u * s : GL (Fin 6) (ZMod 2)) : Mat6) := by
    intro r hr
    obtain ⟨u, hu⟩ := hunit (3 + r) (by omega)
    rw [getD_mats.2 r hr] at hu
    refine ⟨u, hu, fun c hc => ?_⟩
    have h' := hreach (r + 1) (by omega) c hc
    rw [hrs r hr, hm (3 + r) (by omega), getD_mats.2 r hr] at h'
    have hl := hL' r hr
    rw [hm (3 + r) (by omega), getD_mats.2 r hr] at hl
    obtain ⟨er, hrlt⟩ := decF_actT (hvG r hr) hl hW15
    refine reach_inv (P := fun x => x < 2 ^ 15 ∧ ∃ s ∈ genSubN 6 sbGens,
        decF x = ((u * s : GL (Fin 6) (ZMod 2)) : Mat6)ᵀ * decN 6 w0c *
          ((u * s : GL (Fin 6) (ZMod 2)) : Mat6))
      (fun s hs x hx => ?_) ⟨hrlt, 1, one_mem _, ?_⟩ h'
    · obtain ⟨hxl, t, ht, ex⟩ := hx
      obtain ⟨e, hlt⟩ := hact s hs x hxl
      obtain ⟨v, hvm, hvv⟩ := huS s hs
      refine ⟨hlt, t * v, mul_mem ht hvm, ?_⟩
      rw [e, ex, ← hvv, ← mul_assoc u t v, Units.val_mul (u * t) v, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    · rw [er, hW0, mul_one, hu]
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun r => (T r).map decF, ?_, fun r hr => ?_, ?_,
    fun r hr x hx => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hmemS g hg
    exact hfix' s hs
  · obtain ⟨m, hm8, rfl⟩ := List.getElem_of_mem hg
    rw [← List.getD_eq_getElem _ [] hm8]
    have hl8 : (sbGens ++ grs).length = 8 := rfl
    exact hunit m (by omega)
  · have hl0 : (T 0).length = 1 := by
      have := hlen 0 (by norm_num)
      have := hST 0 (by norm_num)
      simp only [List.getD_cons_zero] at this
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hl0
    have hc0 := (inv0 c (by rw [hc]; exact List.mem_singleton_self c)).2
    simp only [hc, List.map_cons, List.map_nil, hc0]
  · have := hlen (r + 1) (by omega)
    have := hST (r + 1) (by omega)
    rw [List.length_map]
    simp only [List.getD_cons_succ] at this
    omega
  · rw [← List.map_flatMap]
    refine hnd.map_on fun a ha b hb e => ?_
    have hlt : ∀ c ∈ (List.range 6).flatMap T, c < 2 ^ 15 := by
      intro c hc
      obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp hc
      rw [List.mem_range] at hr
      rcases r with _ | r
      · exact (inv0 c hc).1
      · obtain ⟨u, -, hu⟩ := invr r (by omega)
        exact (hu c hc).1
    exact decF_inj (hlt a ha) (hlt b hb) e
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, hT⟩ := invr r hr
    obtain ⟨-, s, hs, e⟩ := hT c hc
    exact ⟨u, hu, s, hs, e⟩

end Form

end CFSG.KC.Sp6Over

end
