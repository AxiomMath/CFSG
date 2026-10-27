module

public import CFSG.Certificates.Kernel.Spor.PK.O73Parse
public import CFSG.Certificates.Kernel.Spor.PK.O73Tab
public import CFSG.Certificates.Kernel.Misc.O73Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73
  CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native Matrix

private theorem o73_matK {VL : List (List ℕ)} {Ts Rs : List ℕ} (hm : matK VL Ts Rs = true) :
    Ts.length = 8 ∧ Rs.length = 8 ∧ ∀ i < 8,
      Ts.getD i 0 = tK (VL.getD i []) ∧ Rs.getD i 0 = rK (VL.getD i []) ∧
      q3K (VL.getD i []) = 2 ∧ mulM7 (Ts.getD i 0) (Ts.getD i 0) = oneM7 ∧
      mulM7 (Rs.getD i 0) (Rs.getD i 0) = oneM7 ∧
      mulM7 (trM7 (Ts.getD i 0)) (mulM7 gramM (Ts.getD i 0)) = gramM := by
  unfold matK at hm
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq, allN_lqt_iff, letB_eq, nthN_eq,
    nthL_eq] at hm
  obtain ⟨h1, h2, h3⟩ := hm
  refine ⟨h1, h2, fun i hi => ?_⟩
  obtain ⟨a, b, c, d, e, f⟩ := h3 i hi
  exact ⟨a, b, c, d, e, f⟩

private theorem o73_relMK {Ts Rs : List ℕ} {R1 E : List (List ℕ)} (hr : relMK Ts Rs R1 E = true) :
    (∀ w ∈ R1, wordM7 Ts w = oneM7 ∧ wordM7 Rs w = oneM7) ∧ ∀ w ∈ E, wordM7 Ts w = oneM7 := by
  unfold relMK at hr
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, allLL_iff] at hr
  exact hr

private theorem o73_list_eq {Ts : List ℕ} (F : Fin 8 → Matrix Idx Idx (ZMod 3))
    (hlen : Ts.length = 8) (h : ∀ i : Fin 8, Ts.getD i 0 = mEnc (F i)) :
    Ts = (List.ofFn F).map mEnc := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi : i < 8 := hlen ▸ h1
    have := h ⟨i, hi⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
    rw [List.getElem_map, List.getElem_ofFn]
    exact this

private theorem o73_tab_eq (F : Fin 8 → Matrix Idx Idx (ZMod 3)) :
    (Array.ofFn fun i : Fin 8 => tabOf (F i)) = ((List.ofFn F).map tabOf).toArray := by
  apply Array.ext'
  simp [Array.toList_ofFn, List.map_ofFn]

private theorem o73_relatorsOK_tab (Ms : List (Matrix Idx Idx (ZMod 3))) (rels : List (List ℕ))
    (h : ∀ w ∈ rels, wordMat Ms w = 1) : relatorsOK 2187 (Ms.map tabOf).toArray rels = true := by
  unfold relatorsOK
  rw [List.all_eq_true]
  intro w hw
  rw [evalW_tabOf, h w hw, ← tabOf_one]
  exact (eqA_tabOf_iff 1 1).2 rfl

private theorem o73_getD_lt {a : Array ℕ} {n w : ℕ} (hn : a.size = n)
    (hlt : ∀ x ∈ a.toList, x < 2 ^ w) : ∀ i < n, a.toList.getD i 0 < 2 ^ w := by
  intro i hi
  have hi' : i < a.toList.length := by simpa [hn] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  exact hlt _ (List.getElem_mem hi')

private theorem o73_unpack_eq {a : Array ℕ} {n w : ℕ} (hn : a.size = n)
    (hlt : ∀ x ∈ a.toList, x < 2 ^ w) :
    unpackA n w (enc w (fun j => a.toList.getD j 0) n) = a := by
  apply Array.ext
  · simp [unpackA, hn]
  · intro j h1 h2
    have hj : j < n := by simpa [unpackA] using h1
    have hj' : j < a.toList.length := by simpa [hn] using hj
    simp only [unpackA, Array.getElem_ofFn]
    rw [fd_enc (o73_getD_lt hn hlt) hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
      Option.getD_some]
    simp

private theorem o73_lineVal {w n P : ℕ} {a : Array ℕ} (ha : a.size < 2 ^ 16)
    (h1 : Nat.land (lineVal w a.toList) 65535 = n)
    (h2 : Nat.shiftRight (lineVal w a.toList) 16 = P) :
    a.size = n ∧ P = enc w (fun j => a.toList.getD j 0) n := by
  have e1 : lineVal w a.toList =
      a.size + 2 ^ 16 * enc w (fun j => a.toList.getD j 0) a.size := by
    simp [lineVal]
  rw [e1] at h1 h2
  have h1' : (a.size + 2 ^ 16 * enc w (fun j => a.toList.getD j 0) a.size) % 2 ^ 16 = n := by
    rw [← Nat.and_two_pow_sub_one_eq_mod]
    exact h1
  have h2' : (a.size + 2 ^ 16 * enc w (fun j => a.toList.getD j 0) a.size) / 2 ^ 16 = P := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact h2
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha] at h1'
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 16), Nat.div_eq_of_lt ha, Nat.zero_add] at h2'
  subst h1'
  exact ⟨rfl, h2'.symm⟩

private theorem o73_lines {cs : List ℕ} {w n m : ℕ} {Ps : List ℕ}
    (hf : fmtK cs = true) (ht : tokLt (2 ^ w) cs = true) (hlen : cs.length < 2 ^ 16)
    (hl : linesK n m (parseK w cs) Ps = true) :
    (textLines (strL cs)).map parseNats = Ps.map (unpackA n w) ∧ Ps.length = m ∧
      ∀ P ∈ Ps, P < 2 ^ (w * n) := by
  rw [parseK_eq hf ht] at hl
  unfold linesK at hl
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq, allN_lqt_iff, letB_eq, nthN_eq,
    List.length_map] at hl
  obtain ⟨hL, hP, hi⟩ := hl
  have hent := parseNats_lt_of_tokLt hf ht
  have hlen_i : ∀ line ∈ textLines (strL cs), (parseNats line).size < 2 ^ 16 := fun line hline =>
    Nat.lt_of_le_of_lt (length_parseNats_le hf line hline) hlen
  have key : ∀ (i : ℕ) (hi' : i < (textLines (strL cs)).length),
      (parseNats (textLines (strL cs))[i]).size = n ∧
      Ps.getD i 0 = enc w (fun j => (parseNats (textLines (strL cs))[i]).toList.getD j 0) n := by
    intro i hi'
    have him : i < m := hL ▸ hi'
    obtain ⟨h1, h2⟩ := hi i him
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi'] at h1 h2
    simp only [Option.map_some, Option.getD_some] at h1 h2
    exact o73_lineVal (hlen_i _ (List.getElem_mem hi')) h1 h2
  have hsz : ∀ (i : ℕ) (hi' : i < (textLines (strL cs)).length),
      unpackA n w (Ps.getD i 0) = parseNats (textLines (strL cs))[i] := by
    intro i hi'
    obtain ⟨k1, k2⟩ := key i hi'
    rw [k2]
    exact o73_unpack_eq k1 (hent _ (List.getElem_mem hi'))
  refine ⟨?_, hP, ?_⟩
  · apply List.ext_getElem
    · simp [hL, hP]
    · intro i h1 h2
      have h1' : i < (textLines (strL cs)).length := by simpa using h1
      have h2' : i < Ps.length := by simpa using h2
      rw [List.getElem_map, List.getElem_map, ← hsz i h1', List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h2', Option.getD_some]
  · intro P hPm
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.1 hPm
    have hi'' : i < (textLines (strL cs)).length := by rw [hL, ← hP]; exact hi'
    obtain ⟨k1, k2⟩ := key i hi''
    have e : Ps[i] = Ps.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [e, k2]
    exact enc_lt (o73_getD_lt k1 (hent _ (List.getElem_mem hi'')))

private theorem o73_wordPF_lt {n w : ℕ} (Ps : List ℕ)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List ℕ) :
    ∀ x < n, wordPF w Ps wd x < n := by
  induction wd with
  | nil => intro x hx; exact hx
  | cons c wd ih =>
    intro x hx
    show (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd x) else wordPF w Ps wd x) < n
    by_cases hc : c < Ps.length
    · rw [if_pos hc]
      exact hPs c hc _ (ih x hx)
    · rw [if_neg hc]
      exact ih x hx

private theorem o73_wordP_lt {n w : ℕ} (hw : n ≤ 2 ^ w) (Ps : List ℕ)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List ℕ) :
    CFSG.KC.Misc.O73.wordP n w Ps wd < 2 ^ (w * n) := by
  rw [wordP_eq_of_maps hw Ps hPs wd]
  exact enc_lt fun i hi => Nat.lt_of_lt_of_le (o73_wordPF_lt Ps hPs wd i hi) hw

private theorem o73_idP_lt {n w : ℕ} (hw : n ≤ 2 ^ w) : idP n w < 2 ^ (w * n) := by
  rw [idP_eq hw]
  exact enc_lt fun i hi => Nat.lt_of_lt_of_le hi hw

private theorem o73_relPK {LP : List ℕ} {E : List (List ℕ)} {k : ℕ} (h : relPK LP E k 1 = true)
    (hk : k < E.length) :
    CFSG.KC.Misc.O73.wordP 1134 11 LP E[k] = idP 1134 11 := by
  unfold relPK at h
  simp only [allN_lqt_iff, letB_eq, impB_eq, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq,
    Nat.beq_eq, lenLLN_eq, nthL_eq] at h
  have h0 := h 0 (by norm_num)
  have e : k.add 0 = k := rfl
  rw [e] at h0
  rcases h0 with h0 | h0
  · have hb : Nat.blt k E.length = true := by rw [Nat.blt_eq]; exact hk
    rw [h0] at hb
    exact absurd hb (by decide)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at h0
    exact h0

private theorem o73_lifts {cL LP : List ℕ} {E : List (List ℕ)} {sp : List ℕ} {nE : ℕ}
    (hl : liftTextK cL LP = true) (hE : ∀ k < nE, relPK LP E k 1 = true)
    (hnE : relPK.lenLLN E ≤ nE) (hs : spK LP sp = true) (hcL : cL.length < 2 ^ 16) :
    (parsePerms (strOf cL)).size = 8 ∧ permsOK 1134 (parsePerms (strOf cL)) = true ∧
      relatorsOK 1134 (parsePerms (strOf cL)) E = true ∧
      eqA 1134 (evalW 1134 (parsePerms (strOf cL)) sp) (idA 1134) = false := by
  unfold liftTextK at hl
  simp only [andB_eq, Bool.and_eq_true, allN_lqt_iff, nthN_eq] at hl
  obtain ⟨hf, ht, hlines, hperm⟩ := hl
  have ht' : tokLt (2 ^ 11) cL = true := ht
  obtain ⟨hmap, hLP, -⟩ := o73_lines hf ht' hcL hlines
  have hP : parsePerms (strOf cL) = (LP.map (unpackA 1134 11)).toArray := by
    show ((textLines (strL cL)).map parseNats).toArray = _
    rw [hmap]
  have hperm' : ∀ P ∈ LP, permK 1134 11 P = true := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hP
    have := hperm i (hLP ▸ hi)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  have hw : (1134 : ℕ) ≤ 2 ^ 11 := by norm_num
  have hPs : ∀ c < LP.length, ∀ x < 1134, fd 11 (LP.getD c 0) x < 1134 := by
    intro c hc x hx
    have hc0 : LP.getD c 0 = LP[c] := by simp [List.getD_eq_getElem?_getD, hc]
    rw [hc0]
    exact ((permK_iff.1 (hperm' _ (List.getElem_mem hc))).2).1 x hx
  rw [hP]
  refine ⟨by simp [hLP], permsOK_unpack hperm', ?_, ?_⟩
  · unfold relatorsOK
    rw [List.all_eq_true]
    intro w hw'
    rw [evalW_unpack hw hperm' w]
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw'
    have hk' : k < nE := by
      have := lenLLN_eq E
      omega
    rw [o73_relPK (hE k hk') hk]
    exact (eqA_unpack_idP hw (o73_idP_lt hw)).2 rfl
  · rw [Bool.eq_false_iff]
    intro h
    rw [evalW_unpack hw hperm' sp] at h
    have h1 := (eqA_unpack_idP hw (o73_wordP_lt hw LP hPs sp)).1 h
    unfold spK at hs
    rw [h1] at hs
    simp at hs

private theorem o73_betaK {Rs cB cY YP : List ℕ} {BP : ℕ} (hb : betaK Rs cB cY BP YP = true) :
    fmtK cB = true ∧ tokLt 4096 cB = true ∧ linesK 728 1 (parseK 12 cB) [BP] = true ∧
    fmtK cY = true ∧ tokLt 1024 cY = true ∧ linesK 728 8 (parseK 10 cY) YP = true ∧
    (∀ x < 728, at' 12 BP x < 2187) ∧
    (Nat.rec (motive := fun _ => Nat) 0
        (fun x acc => Nat.add acc (Nat.shiftLeft 1 (at' 12 BP x))) 728 =
      Nat.rec (motive := fun _ => Nat) 0
        (fun x acc => Nat.lor acc (Nat.shiftLeft 1 (at' 12 BP x))) 728) ∧
    (∀ i < 8, ∀ x < 728,
      appM7 (Rs.getD i 0) (at' 12 BP x) = at' 12 BP (at' 10 (YP.getD i 0) x)) := by
  unfold betaK at hb
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, allN_lqt_iff, letB_eq, nthN_eq,
    Nat.blt_eq] at hb
  exact hb

private theorem o73_or_pow (D k : ℕ) :
    D ||| 2 ^ k = if D.testBit k = true then D else D + 2 ^ k := by
  by_cases hb : D.testBit k = true
  · rw [if_pos hb]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hj : k = j
    · subst hj
      simp [hb]
    · simp [hj]
  · rw [if_neg hb]
    have hb' : D.testBit k = false := by simpa using hb
    have hD := Nat.div_add_mod D (2 ^ (k + 1))
    have hL1 : D % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hLk : (D % 2 ^ (k + 1)).testBit k = false := by
      have h := Nat.testBit_two_pow_mul_add (D / 2 ^ (k + 1)) hL1 k
      rw [if_pos (Nat.lt_succ_self k), hD] at h
      rw [← h]
      exact hb'
    have hL : D % 2 ^ (k + 1) < 2 ^ k := by
      refine Nat.lt_pow_two_of_testBit _ (fun i hi => ?_)
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact hLk
      · exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hL1 (Nat.pow_le_pow_right (by norm_num) hlt))
    have h2 : D % 2 ^ (k + 1) + 2 ^ k < 2 ^ (k + 1) := by omega
    calc D ||| 2 ^ k
        = ((2 ^ (k + 1) * (D / 2 ^ (k + 1))) ||| D % 2 ^ (k + 1)) ||| 2 ^ k := by
          rw [← Nat.two_pow_add_eq_or_of_lt hL1, hD]
      _ = (2 ^ (k + 1) * (D / 2 ^ (k + 1))) ||| (D % 2 ^ (k + 1) ||| 2 ^ k) := by
          rw [Nat.or_assoc]
      _ = (2 ^ (k + 1) * (D / 2 ^ (k + 1))) ||| (D % 2 ^ (k + 1) + 2 ^ k) := by
          rw [Nat.or_two_pow_eq_add_of_lt hL]
      _ = 2 ^ (k + 1) * (D / 2 ^ (k + 1)) + (D % 2 ^ (k + 1) + 2 ^ k) :=
          (Nat.two_pow_add_eq_or_of_lt h2 _).symm
      _ = D + 2 ^ k := by rw [← Nat.add_assoc, hD]

private theorem o73_sl1 (k : ℕ) : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k

private theorem o73_testBit_orPow (f : ℕ → ℕ) (n j : ℕ) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) n).testBit j = true ↔
      ∃ i < n, f i = j := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) n) (Nat.shiftLeft 1 (f n))).testBit j
        = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, o73_sl1, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

private def o73_S (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.add acc (Nat.shiftLeft 1 (b x))) n

private def o73_O (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (Nat.shiftLeft 1 (b x))) n

private theorem o73_S_succ (b : ℕ → ℕ) (n : ℕ) : o73_S b (n + 1) = o73_S b n + 2 ^ b n := by
  show Nat.add (o73_S b n) (Nat.shiftLeft 1 (b n)) = _
  rw [o73_sl1]
  rfl

private theorem o73_O_succ (b : ℕ → ℕ) (n : ℕ) : o73_O b (n + 1) = o73_O b n ||| 2 ^ b n := by
  show Nat.lor (o73_O b n) (Nat.shiftLeft 1 (b n)) = _
  rw [o73_sl1]
  rfl

private theorem o73_sum_or (b : ℕ → ℕ) : ∀ n : ℕ, o73_O b n ≤ o73_S b n ∧
    (o73_S b n = o73_O b n → ∀ x < n, ∀ y < n, b x = b y → x = y) := by
  intro n
  induction n with
  | zero => exact ⟨Nat.le_refl _, fun _ x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ n ih =>
    obtain ⟨hle, hinj⟩ := ih
    rw [o73_S_succ, o73_O_succ, o73_or_pow]
    have hp : 0 < 2 ^ b n := Nat.two_pow_pos _
    refine ⟨?_, ?_⟩
    · split <;> omega
    · intro heq
      by_cases hbit : (o73_O b n).testBit (b n) = true
      · rw [if_pos hbit] at heq
        omega
      · rw [if_neg hbit] at heq
        have hSO : o73_S b n = o73_O b n := by omega
        have hfree : ∀ y < n, b y ≠ b n := by
          intro y hy hyn
          exact hbit ((o73_testBit_orPow b n _).2 ⟨y, hy, hyn⟩)
        intro x hx y hy hxy
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · exact hinj hSO x hx y hy hxy
        · exact absurd hxy (hfree x hx)
        · exact absurd hxy.symm (hfree y hy)
        · rfl

private theorem o73_getElem!_ofFn {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem o73_map_toArray_get {α β : Type} [Inhabited β] (f : α → β) (L : List α) {c : ℕ}
    (hc : c < L.length) : (L.map f).toArray[c]! = f L[c] := by
  rw [getElem!_pos _ _ (by simpa using hc)]
  simp

private theorem o73_unpack_get {n w P : ℕ} (hP : P < 2 ^ (w * n)) (i : ℕ) :
    (unpackA n w P)[i]! = fd w P i := by
  by_cases hi : i < n
  · rw [unpackA, o73_getElem!_ofFn _ hi]
  · rw [getElem!_neg _ _ (by simpa [unpackA] using hi)]
    have h1 : 2 ^ (w * n) ≤ 2 ^ (w * i) :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left w (Nat.le_of_not_lt hi))
    unfold fd
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP h1), Nat.zero_mod]
    rfl

private theorem o73_sum_or' (b : ℕ → ℕ) (n : ℕ)
    (h : Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.add acc (Nat.shiftLeft 1 (b x))) n =
      Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (Nat.shiftLeft 1 (b x))) n) :
    ∀ x < n, ∀ y < n, b x = b y → x = y :=
  (o73_sum_or b n).2 h

private theorem o73_beta {VL : List (List ℕ)} {Rs cB cY YP : List ℕ} {BP : ℕ}
    (hb : betaK Rs cB cY BP YP = true) (hRs : ∀ i : Fin 8, Rs.getD i 0 = mEnc (rMat (vecsG VL i)))
    (hcB : cB.length < 2 ^ 16) (hcY : cY.length < 2 ^ 16) (hcB10 : 10 ∉ cB) :
    (parseNats (strOf cB)).size = 728 ∧ (∀ x : Fin 728, (parseNats (strOf cB))[x.val]! < 2187) ∧
      (∀ x y : Fin 728, (parseNats (strOf cB))[x.val]! = (parseNats (strOf cB))[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
        ((rTabsG VL)[i.val]!)[(parseNats (strOf cB))[x.val]!]! =
          (parseNats (strOf cB))[((parsePerms (strOf cY))[i.val]!)[x.val]!]! := by
  obtain ⟨hfB, htB, hlB, hfY, htY, hlY, hlt, hso, hrel⟩ := o73_betaK hb
  have htB' : tokLt (2 ^ 12) cB = true := htB
  have htY' : tokLt (2 ^ 10) cY = true := htY
  obtain ⟨hmapB, -, hltB⟩ := o73_lines hfB htB' hcB hlB
  obtain ⟨hmapY, hYP, hltY⟩ := o73_lines hfY htY' hcY hlY
  have hBPlt : BP < 2 ^ (12 * 728) := hltB BP (by simp)
  have h128 : ∀ c ∈ cB, c < 128 := by
    intro c hc
    have := (fmtK_iff cB).1 hfB c hc
    omega
  have hsplit : (strL cB).splitOn "\n" = [strL cB] := by
    rw [splitOn_newline_strL h128, List.splitOn_eq_singleton hcB10]
    rfl
  have hL1 : (textLines (strL cB)).length = 1 := by
    have := congrArg List.length hmapB
    simpa using this
  have htl : textLines (strL cB) = [strL cB] := by
    unfold textLines at hL1 ⊢
    rw [hsplit] at hL1 ⊢
    by_cases he : (!(strL cB).isEmpty) = true
    · simp [he]
    · simp [he] at hL1
  have hβ : parseNats (strOf cB) = unpackA 728 12 BP := by
    have := hmapB
    rw [htl] at this
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
    exact this
  have hPY : parsePerms (strOf cY) = (YP.map (unpackA 728 10)).toArray := by
    show ((textLines (strL cY)).map parseNats).toArray = _
    rw [hmapY]
  have hget : ∀ y : ℕ, (parseNats (strOf cB))[y]! = at' 12 BP y := by
    intro y
    rw [hβ, o73_unpack_get hBPlt, at'_eq]
  refine ⟨by rw [hβ]; simp [unpackA], fun x => ?_, fun x y hxy => ?_, fun i x => ?_⟩
  · rw [hget]
    exact hlt x x.2
  · rw [hget, hget] at hxy
    exact Fin.ext (o73_sum_or' (fun x => at' 12 BP x) 728 hso x x.2 y y.2 hxy)
  · have hβx : at' 12 BP x < 2187 := hlt x x.2
    have hRi := hrel i.val i.2 x x.2
    rw [hRs i] at hRi
    have hiY : i.val < YP.length := by rw [hYP]; exact i.2
    have hYmem : YP.getD i.val 0 ∈ YP := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiY, Option.getD_some]
      exact List.getElem_mem hiY
    have hrT : (rTabsG VL)[i.val]! = tabOf (rMat (vecsG VL i)) := by
      unfold rTabsG
      exact o73_getElem!_ofFn (fun i : Fin 8 => tabOf (rMat (vecsG VL i))) i.2
    have hYi : (parsePerms (strOf cY))[i.val]! = unpackA 728 10 (YP.getD i.val 0) := by
      rw [hPY, o73_map_toArray_get _ _ hiY, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hiY, Option.getD_some]
    simp only [hget]
    rw [hrT, hYi, o73_unpack_get (hltY _ hYmem), ← at'_eq, tabOf_get _ hβx]
    exact (appM7_mEnc _ hβx).symm.trans hRi

private theorem o73_wordMat_eq_one {Ms : List (Matrix Idx Idx (ZMod 3))} {Ts : List ℕ}
    (hTs : Ts = Ms.map mEnc) {w : List ℕ} (h : wordM7 Ts w = oneM7) : wordMat Ms w = 1 := by
  rw [hTs, wordM7_mEnc, oneM7_eq] at h
  exact mEnc_inj h

theorem o73_sound' {VL : List (List ℕ)} {R1 E : List (List ℕ)} {sp : List ℕ}
    {Ts Rs cL cB cY LP YP : List ℕ} {BP nE : ℕ}
    (hm : matK VL Ts Rs = true) (hr : relMK Ts Rs R1 E = true)
    (hl : liftTextK cL LP = true) (hE : ∀ k < nE, relPK LP E k 1 = true)
    (hnE : relPK.lenLLN E ≤ nE) (hs : spK LP sp = true)
    (hb : betaK Rs cB cY BP YP = true) (hcL : cL.length < 2 ^ 16) (hcB : cB.length < 2 ^ 16)
    (hcY : cY.length < 2 ^ 16) (hcB10 : 10 ∉ cB) :
    ((∀ i : Fin 8, q3 (vecsG VL i) = 2) ∧ (tTabsG VL).size = 8 ∧ (rTabsG VL).size = 8 ∧
      (∀ i : Fin 8, tMat (vecsG VL i) * tMat (vecsG VL i) = 1 ∧
        rMat (vecsG VL i) * rMat (vecsG VL i) = 1) ∧
      permsOK 2187 (tTabsG VL) = true ∧ permsOK 2187 (rTabsG VL) = true ∧
      (∀ i : Fin 8, ∀ x : Fin 2187, q3 (tMat (vecsG VL i) *ᵥ dec x) = q3 (dec x)))
    ∧ (relatorsOK 2187 (tTabsG VL) (R1 ++ E) = true ∧ relatorsOK 2187 (rTabsG VL) R1 = true ∧
      (parsePerms (strOf cL)).size = 8 ∧ permsOK 1134 (parsePerms (strOf cL)) = true ∧
      relatorsOK 1134 (parsePerms (strOf cL)) E = true ∧
      eqA 1134 (evalW 1134 (parsePerms (strOf cL)) sp) (idA 1134) = false)
    ∧ ((parseNats (strOf cB)).size = 728 ∧ (∀ x : Fin 728, (parseNats (strOf cB))[x.val]! < 2187) ∧
      (∀ x y : Fin 728, (parseNats (strOf cB))[x.val]! = (parseNats (strOf cB))[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
        ((rTabsG VL)[i.val]!)[(parseNats (strOf cB))[x.val]!]! =
          (parseNats (strOf cB))[((parsePerms (strOf cY))[i.val]!)[x.val]!]!) := by
  obtain ⟨hTlen, hRlen, hmat⟩ := o73_matK hm
  have hT : ∀ i : Fin 8, Ts.getD i 0 = mEnc (tMat (vecsG VL i)) := fun i => by
    rw [(hmat i i.2).1, tK_eq]
    rfl
  have hR : ∀ i : Fin 8, Rs.getD i 0 = mEnc (rMat (vecsG VL i)) := fun i => by
    rw [(hmat i i.2).2.1, rK_eq]
    rfl
  have hq : ∀ i : Fin 8, q3 (vecsG VL i) = 2 := fun i => by
    have h := (hmat i i.2).2.2.1
    rw [q3K_eq] at h
    have h2 : (q3 (vecOf (VL.getD i []))).val = (2 : ZMod 3).val := h
    exact ZMod.val_injective 3 h2
  have hTT : ∀ i : Fin 8, tMat (vecsG VL i) * tMat (vecsG VL i) = 1 := fun i => by
    have h := (hmat i i.2).2.2.2.1
    rw [hT i, mulM7_mEnc, oneM7_eq] at h
    exact mEnc_inj h
  have hRR : ∀ i : Fin 8, rMat (vecsG VL i) * rMat (vecsG VL i) = 1 := fun i => by
    have h := (hmat i i.2).2.2.2.2.1
    rw [hR i, mulM7_mEnc, oneM7_eq] at h
    exact mEnc_inj h
  have hpol : ∀ i : Fin 8, (tMat (vecsG VL i))ᵀ * gram * tMat (vecsG VL i) = gram := fun i => by
    have h := (hmat i i.2).2.2.2.2.2
    rw [hT i, trM7_mEnc, gramM_eq, mulM7_mEnc, mulM7_mEnc] at h
    rw [Matrix.mul_assoc]
    exact mEnc_inj h
  have hTs : Ts = (List.ofFn fun i : Fin 8 => tMat (vecsG VL i)).map mEnc :=
    o73_list_eq _ hTlen hT
  have hRs : Rs = (List.ofFn fun i : Fin 8 => rMat (vecsG VL i)).map mEnc :=
    o73_list_eq _ hRlen hR
  have htT : tTabsG VL = ((List.ofFn fun i : Fin 8 => tMat (vecsG VL i)).map tabOf).toArray :=
    o73_tab_eq fun i : Fin 8 => tMat (vecsG VL i)
  have hrT : rTabsG VL = ((List.ofFn fun i : Fin 8 => rMat (vecsG VL i)).map tabOf).toArray :=
    o73_tab_eq fun i : Fin 8 => rMat (vecsG VL i)
  obtain ⟨hrel1, hrel2⟩ := o73_relMK hr
  refine ⟨⟨hq, ?_, ?_, fun i => ⟨hTT i, hRR i⟩, ?_, ?_, fun i x => ?_⟩, ⟨?_, ?_, ?_⟩,
    o73_beta hb hR hcB hcY hcB10⟩
  · exact Array.size_ofFn
  · exact Array.size_ofFn
  · rw [htT]
    refine permsOK_tabOf _ fun M hM => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hM
    exact hTT i
  · rw [hrT]
    refine permsOK_tabOf _ fun M hM => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hM
    exact hRR i
  · exact q3_mulVec (hpol i) _
  · rw [htT]
    refine o73_relatorsOK_tab _ _ fun w hw => ?_
    rcases List.mem_append.1 hw with h | h
    · exact o73_wordMat_eq_one hTs (hrel1 w h).1
    · exact o73_wordMat_eq_one hTs (hrel2 w h)
  · rw [hrT]
    exact o73_relatorsOK_tab _ _ fun w hw => o73_wordMat_eq_one hRs (hrel1 w hw).2
  · exact o73_lifts hl hE hnE hs hcL

end CFSG.KS.PK

end
