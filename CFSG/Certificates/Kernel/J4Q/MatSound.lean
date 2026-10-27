module

public import Certificates.Data.Kernel.J4Q.MatChk
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.J4.Setup
import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.SporSch.J4SBigSound

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

private theorem lt64 (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

private theorem v2N_testBit (v : V2) (k : Nat) :
    (v2N v).testBit k = if k < 64 then v.lo.toNat.testBit k else v.hi.toNat.testBit (k - 64) := by
  change (v.lo.toNat ||| (v.hi.toNat <<< 64)).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < 64
  · have h1 : ¬ k ≥ 64 := by omega
    simp [hk, h1]
  · have h1 : k ≥ 64 := by omega
    have h2 : v.lo.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64 v.lo) (Nat.pow_le_pow_right (by omega) h1))
    simp [hk, h1, h2]

private theorem shl_one_toNat (j : Nat) :
    ((1 : UInt64) <<< UInt64.ofNat (j % 64)).toNat = 2 ^ (j % 64) := by
  have hj : j % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  have e1 : j % 64 % 2 ^ 64 % 64 = j % 64 := by
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj (by decide)), Nat.mod_eq_of_lt hj]
  rw [e1, UInt64.toNat_one, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hj)

private theorem setBit_bits (v : V2) {j : Nat} (hj : j < 112) (k : Nat) :
    (v2N (v.setBit j)).testBit k = ((v2N v).testBit k || decide (k = j)) := by
  unfold V2.setBit
  by_cases h : j / 64 = 0
  · simp only [h, ↓reduceIte]
    rw [v2N_testBit, v2N_testBit]
    have hj' : j < 64 := by omega
    have hm : j % 64 = j := Nat.mod_eq_of_lt hj'
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNat, hm, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        simp
      · have e' : ¬ j = k := fun h => e h.symm
        simp [e, e']
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
  · simp only [h, ↓reduceIte]
    rw [v2N_testBit, v2N_testBit]
    have hj' : 64 ≤ j := by omega
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNat, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        have : k % 64 = k - 64 := by omega
        simp [this]
      · have e' : ¬ j % 64 = k - 64 := by omega
        simp [e, e']

private theorem ofFn_bits (f : Nat → Bool) (k : Nat) :
    (v2N (V2.ofFn f)).testBit k = (decide (k < 112) && f k) := by
  have key : ∀ m ≤ 112, (v2N ((List.range m).foldl
      (fun v j => if f j then v.setBit j else v) V2.zero)).testBit k = (decide (k < m) && f k) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : v2N V2.zero = 0 := rfl
      simp [this]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hf : f m
      · simp only [hf, ↓reduceIte]
        rw [setBit_bits _ (by omega), ih (by omega)]
        by_cases e : k = m
        · subst e
          simp [hf]
        · have h1 : (k < m + 1) ↔ k < m := by omega
          simp [e, h1]
      · have hf' : f m = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, ↓reduceIte]
        rw [ih (by omega)]
        by_cases e : k = m
        · subst e
          simp [hf]
        · have h1 : (k < m + 1) ↔ k < m := by omega
          simp [h1]
  exact key 112 (Nat.le_refl _)

private theorem ofBits_bits (f : Nat → Bool) (k : Nat) :
    (CFSG.Sporadic.SmallF2.Native.ofBits 112 f).testBit k = (decide (k < 112) && f k) := by
  have key : ∀ m, ((List.range m).foldl
      (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0).testBit k =
      (decide (k < m) && f k) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hf : f m
      · simp only [hf, ↓reduceIte]
        rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
        by_cases e : k = m
        · subst e
          simp [hf]
        · have e' : ¬ m = k := fun h => e h.symm
          have h1 : (k < m + 1) ↔ k < m := by omega
          simp [e', h1]
      · have hf' : f m = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        by_cases e : k = m
        · subst e
          simp [hf']
        · have h1 : (k < m + 1) ↔ k < m := by omega
          simp [h1]
  exact key 112

private theorem v2N_ofFn (f : Nat → Bool) :
    v2N (V2.ofFn f) = CFSG.Sporadic.SmallF2.Native.ofBits 112 f :=
  Nat.eq_of_testBit_eq fun k => by rw [ofFn_bits, ofBits_bits]

private theorem enc_congr {X : Array V2} {Y : Array Nat}
    (h : ∀ i < 112, v2N (X.getD i V2.zero) = Y.getD i 0) :
    encR X = CFSG.KS.SporSch.J4B.encN Y := by
  unfold encR CFSG.KS.SporSch.J4B.encN
  suffices H : ∀ l : List Nat, (∀ i ∈ l, i < 112) →
      l.foldr (fun i acc => Nat.lor (Nat.shiftLeft (v2N (X.getD i V2.zero)) (128 * i)) acc) 0 =
      l.foldr (fun i acc => Nat.lor (Nat.shiftLeft (Y.getD i 0) (128 * i)) acc) 0 from
    H _ (fun i hi => List.mem_range.1 hi)
  intro l hl
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, h i (hl i List.mem_cons_self),
      ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]

private theorem seed_enc {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Nat} {l : List Char}
    (h : decOK M l = true) :
    WfA (rowsOf (String.ofList l)) ∧ encR (rowsOf (String.ofList l)) = M := by
  obtain ⟨-, hE⟩ := CFSG.KS.SporSch.J4B.decode_enc hK h
  have e1 : CFSG.Sporadic.J4Schreier.O.decode (String.ofList l) =
      Array.ofFn (n := 112) fun i => CFSG.Sporadic.SmallF2.Native.ofBits 112 fun j =>
        ((CFSG.Sporadic.Th.Native.decodeEntries (String.ofList l)).toArray[i.val * 112 + j]?.getD 0)
          % 2 == 1 := rfl
  have e2 : rowsOf (String.ofList l) = Array.ofFn (n := 112) fun i => V2.ofFn fun j =>
      ((CFSG.Sporadic.Th.Native.decodeEntries (String.ofList l)).toArray[i.val * 112 + j]?.getD 0)
        % 2 == 1 := rfl
  refine ⟨⟨by rw [e2, Array.size_ofFn], ?_⟩, ?_⟩
  · rw [e2, Array.all_eq_true]
    intro i hi
    rw [Array.getElem_ofFn]
    exact wf_of_bits (fun k hk => by
      rw [ofFn_bits]
      have : ¬ k < 112 := by omega
      simp [this])
  · rw [← hE]
    apply enc_congr
    intro i hi
    rw [e1, e2]
    simp [Array.getD_eq_getD_getElem?, hi, v2N_ofFn]

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | _ :: _, 0 => rfl
  | m :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact getN_eq d l i

private theorem locRun_sound {D : MatData} {r : Nat} : ∀ (ws : List (List Int)) (L Li : List Nat),
    locRun D r ws L Li = true →
    L.length = ws.length ∧ Li.length = ws.length ∧ ∀ k (hk : k < ws.length),
      L.getD k 0 = wordJ D.c D.rm D.one [D.A, D.B] [D.Ai, D.Bi] ws[k] ∧
      canonJ D.pad (Li.getD k 0) = true ∧
      Nat.beq (mulJ D.c D.rm (L.getD k 0) (Li.getD k 0)) D.one = true
  | [], [], [], _ => ⟨rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | [], [], _ :: _, h => absurd h Bool.false_ne_true
  | [], _ :: _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], h => absurd h Bool.false_ne_true
  | w :: ws, x :: L, xi :: Li, h => by
    change andB (Nat.beq x (wordJ D.c D.rm D.one [D.A, D.B] [D.Ai, D.Bi] w))
      (andB (andB (canonJ D.pad xi) (Nat.beq (mulJ D.c D.rm x xi) D.one))
        (andB (Nat.beq (vecJ D.rm r x) r) (locRun D r ws L Li))) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h⟩ := andB_true h
    obtain ⟨h2a, h2b⟩ := andB_true h2
    obtain ⟨-, h⟩ := andB_true h
    obtain ⟨hl, hli, hk⟩ := locRun_sound ws L Li h
    refine ⟨by simp [hl], by simp [hli], fun k hk' => ?_⟩
    rcases k with _ | k
    · exact ⟨Nat.eq_of_beq_eq_true h1, h2a, h2b⟩
    · simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact hk k (by simpa using hk')

private theorem bm0 : (baseMats ())[0]?.getD (idRows ()) = rowsA () := by
  rw [baseMats, List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some]

private theorem bm1 : (baseMats ())[1]?.getD (idRows ()) = rowsB () := by
  rw [baseMats, List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some]

private theorem bm2 (k : Nat) : (baseMats ())[k + 2]?.getD (idRows ()) = idRows () := by
  rw [baseMats, List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_succ,
    List.getElem?_nil, Option.getD_none]

private theorem bi0 : (baseInvs ())[0]?.getD (idRows ()) = invRows (rowsA ()) := by
  rw [baseInvs, baseMats, List.map_toArray, List.getElem?_toArray, List.map_cons,
    List.getElem?_cons_zero, Option.getD_some]

private theorem bi1 : (baseInvs ())[1]?.getD (idRows ()) = invRows (rowsB ()) := by
  rw [baseInvs, baseMats, List.map_toArray, List.getElem?_toArray, List.map_cons, List.map_cons,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

private theorem bi2 (k : Nat) : (baseInvs ())[k + 2]?.getD (idRows ()) = idRows () := by
  rw [baseInvs, baseMats, List.map_toArray, List.getElem?_toArray, List.map_cons, List.map_cons,
    List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_nil,
    Option.getD_none]

theorem gens_enc (D : MatData) (_hA : seedA = String.ofList D.LA)
    (_hB : seedB = String.ofList D.LB) (_hc : D.consts = true) (_hs : D.seeds = true)
    (_hi : D.invs = true) (_hl : D.loc = true) :
    (∀ k, WfA (baseMats[k]?.getD (idRows ())) ∧
      encR (baseMats[k]?.getD (idRows ())) = getN D.one [D.A, D.B] k) ∧
    (∀ k, WfA (baseInvs[k]?.getD (idRows ())) ∧
      encR (baseInvs[k]?.getD (idRows ())) = getN D.one [D.Ai, D.Bi] k) ∧
    (∀ k, WfA ((locMats ())[k]?.getD (idRows ())) ∧
      encR ((locMats ())[k]?.getD (idRows ())) = getN D.one D.L k) ∧
    (∀ k, WfA ((locInvs ())[k]?.getD (idRows ())) ∧
      encR ((locInvs ())[k]?.getD (idRows ())) = getN D.one D.Li k) := by
  have hK : Consts D.c D.rm D.one D.pad D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6 := _hc
  obtain ⟨hsA, hsB⟩ := andB_true _hs
  obtain ⟨hcan, hmul⟩ := andB_true _hi
  obtain ⟨hcA, hcB⟩ := andB_true hcan
  obtain ⟨hmA, hmB⟩ := andB_true hmul
  have eA : rowsA () = rowsOf (String.ofList D.LA) := by rw [← _hA]; rfl
  have eB : rowsB () = rowsOf (String.ofList D.LB) := by rw [← _hB]; rfl
  obtain ⟨wA, nA⟩ := seed_enc hK hsA
  obtain ⟨wB, nB⟩ := seed_enc hK hsB
  rw [← eA] at wA nA
  rw [← eB] at wB nB
  have hId : WfA (idRows ()) ∧ encR (idRows ()) = D.one := ⟨wf_idRows, enc_idRows hK⟩
  have hm : ∀ k, WfA ((baseMats ())[k]?.getD (idRows ())) ∧
      encR ((baseMats ())[k]?.getD (idRows ())) = getN D.one [D.A, D.B] k := by
    intro k
    rw [getN_eq]
    rcases k with _ | _ | k
    · rw [bm0]
      simpa using ⟨wA, nA⟩
    · rw [bm1]
      simpa using ⟨wB, nB⟩
    · rw [bm2]
      simpa using hId
  have iA := invRows_enc hK wA hcA (by rw [nA]; exact hmA)
  have iB := invRows_enc hK wB hcB (by rw [nB]; exact hmB)
  have hi : ∀ k, WfA ((baseInvs ())[k]?.getD (idRows ())) ∧
      encR ((baseInvs ())[k]?.getD (idRows ())) = getN D.one [D.Ai, D.Bi] k := by
    intro k
    rw [getN_eq]
    rcases k with _ | _ | k
    · rw [bi0]
      simpa using iA
    · rw [bi1]
      simpa using iB
    · rw [bi2]
      simpa using hId
  obtain ⟨hlL, hlLi, hk⟩ := locRun_sound (localWords ()) D.L D.Li _hl
  have hlm : ∀ k, WfA ((locMats ())[k]?.getD (idRows ())) ∧
      encR ((locMats ())[k]?.getD (idRows ())) = getN D.one D.L k := by
    intro k
    rw [getN_eq]
    by_cases hkl : k < (localWords ()).length
    · have e : (locMats ())[k]?.getD (idRows ()) =
          wordRows (baseMats ()) (baseInvs ()) (localWords ())[k] := by
        simp [locMats, hkl]
      rw [e, List.getD_eq_getElem _ _ (by omega)]
      obtain ⟨w1, w2⟩ := enc_wordRows hK hm hi (localWords ())[k]
      refine ⟨w1, ?_⟩
      rw [w2, ← (hk k hkl).1, List.getD_eq_getElem _ _ (by omega)]
    · have e : (locMats ())[k]?.getD (idRows ()) = idRows () := by
        simp [locMats, hkl]
      rw [e, List.getD_eq_default _ _ (by omega)]
      exact hId
  refine ⟨hm, hi, hlm, fun k => ?_⟩
  rw [getN_eq]
  by_cases hkl : k < (localWords ()).length
  · have e : (locInvs ())[k]?.getD (idRows ()) = invRows ((locMats ())[k]?.getD (idRows ())) := by
      have hk2 : k < (locMats ()).size := by simp [locMats, hkl]
      simp [locInvs, hk2]
    obtain ⟨w1, w2⟩ := hlm k
    rw [getN_eq, List.getD_eq_getElem _ _ (by omega)] at w2
    obtain ⟨_, hc2, hm2⟩ := hk k hkl
    rw [List.getD_eq_getElem _ _ (by omega)] at hc2 hm2
    rw [List.getD_eq_getElem _ _ (by omega)] at hm2
    rw [e, List.getD_eq_getElem _ _ (by omega)]
    exact invRows_enc hK w1 hc2 (by rw [w2]; exact hm2)
  · have e : (locInvs ())[k]?.getD (idRows ()) = idRows () := by
      simp [locInvs, locMats, hkl]
    rw [e, List.getD_eq_default _ _ (by omega)]
    exact hId

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private def CanB (M : Nat) : Prop := ∀ p, M.testBit p = true → p < 14336 ∧ p % 128 < 112

private theorem canB_xor {x y : Nat} (hx : CanB x) (hy : CanB y) : CanB (x ^^^ y) := by
  intro p hp
  rw [Nat.testBit_xor] at hp
  cases h1 : x.testBit p
  · rw [h1, Bool.false_xor] at hp
    exact hy p hp
  · exact hx p h1

private theorem canB_and (x : Nat) {y : Nat} (hy : CanB y) : CanB (x &&& y) := by
  intro p hp
  rw [Nat.testBit_and, Bool.and_eq_true] at hp
  exact hy p hp.2

private theorem rep_succ (x s n : Nat) : rep x s (n + 1) = rep x s n ||| x <<< (s * n) := rfl

private theorem rep_one_lt : ∀ n, rep 1 128 n < 2 ^ (128 * n)
  | 0 => by simp [rep]
  | n + 1 => by
    rw [rep_succ, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (rep_one_lt n), Nat.one_shiftLeft]
    have := rep_one_lt n
    have e : 2 ^ (128 * (n + 1)) = 2 ^ (128 * n) * 2 ^ 128 := by rw [← Nat.pow_add]; ring_nf
    rw [e]
    have : 2 ≤ 2 ^ 128 := by norm_num
    nlinarith

private theorem canB_mul_rep {x : Nat} (hx : x < 2 ^ 112) : ∀ n, x * rep 1 128 n < 2 ^ (128 * n) ∧
    ∀ p, (x * rep 1 128 n).testBit p = true → p < 128 * n ∧ p % 128 < 112
  | 0 => by simp [rep]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := canB_mul_rep hx n
    have e : x * rep 1 128 (n + 1) = x <<< (128 * n) + x * rep 1 128 n := by
      rw [rep_succ, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (rep_one_lt n), Nat.one_shiftLeft,
        Nat.shiftLeft_eq]
      ring
    rw [e, Nat.shiftLeft_add_eq_or_of_lt ih1]
    refine ⟨?_, fun p hp => ?_⟩
    · rw [← Nat.shiftLeft_add_eq_or_of_lt ih1, Nat.shiftLeft_eq]
      have e2 : 2 ^ (128 * (n + 1)) = 2 ^ 112 * 2 ^ (128 * n) * 2 ^ 16 := by
        rw [← Nat.pow_add, ← Nat.pow_add]; ring_nf
      rw [e2]
      have h1 : x * 2 ^ (128 * n) + 2 ^ (128 * n) ≤ 2 ^ 112 * 2 ^ (128 * n) := by
        have := Nat.mul_le_mul_right (2 ^ (128 * n)) (Nat.succ_le_of_lt hx)
        rw [Nat.succ_mul] at this
        exact this
      have h2 : 1 ≤ 2 ^ 16 := Nat.one_le_two_pow
      have h3 : 0 < 2 ^ (128 * n) := Nat.two_pow_pos _
      nlinarith
    · rw [Nat.testBit_or, Nat.testBit_shiftLeft] at hp
      rcases Bool.or_eq_true_iff.mp hp with h | h
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h
        have hlt : p - 128 * n < 112 := by
          by_contra hc
          rw [Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num)
            (by omega)))] at h
          exact Bool.false_ne_true h.2
        omega
      · have := ih2 p h
        omega

private theorem canB_mulJ (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (a b : Nat) :
    CanB (mulJ c rm a b) := by
  obtain ⟨hc, hrm⟩ := consts_c hK
  subst hc hrm
  unfold mulJ
  rw [strictN_eq, strictN_eq]
  have hstep : ∀ n, CanB (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => mstep (rep 1 128 112) (2 ^ 112 - 1) a b acc k) n) := by
    intro n
    induction n with
    | zero => intro p hp; simp at hp
    | succ n ih =>
      refine canB_xor ih (canB_and _ ?_)
      have hx : Nat.land (Nat.shiftRight b (Nat.mul n 128)) (2 ^ 112 - 1) < 2 ^ 112 :=
        Nat.and_lt_two_pow _ (by omega)
      intro p hp
      have := (canB_mul_rep hx 112).2 p hp
      omega
  exact hstep 112

private theorem blt_of_bits {M k : Nat} (h : ∀ p, M.testBit p = true → p < k) :
    Nat.blt M (Nat.shiftLeft 1 k) = true := by
  rw [Nat.blt_eq]
  change M < 1 <<< k
  rw [Nat.one_shiftLeft]
  exact Nat.lt_pow_two_of_testBit _ fun p hp => by
    cases e : M.testBit p
    · rfl
    · exact absurd (h p e) (by omega)

private theorem canonJ_of_canB (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Nat}
    (hM : CanB M) : canonJ pad M = true := by
  have hpad := consts_pad hK
  have hz : M &&& pad = 0 := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and, Nat.zero_testBit, hpad]
    cases h : M.testBit p
    · rfl
    · have hp := hM p h
      have e : Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128))
          (Nat.shiftLeft (nat_lit 1) (nat_lit 112)) = (2 ^ 16 - 1) <<< 112 := by decide
      have hrep : ∀ n, (rep ((2 ^ 16 - 1) <<< 112) 128 n).testBit p = true → 112 ≤ p % 128 := by
        intro n
        induction n with
        | zero => intro h0; simp [rep] at h0
        | succ n ih =>
          intro h1
          rw [rep_succ, Nat.testBit_or] at h1
          rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
          · exact ih h1
          · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftLeft,
              Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_two_pow_sub_one,
              decide_eq_true_eq] at h1
            omega
      unfold padMask
      rw [e]
      cases h2 : (rep ((2 ^ 16 - 1) <<< 112) 128 112).testBit p
      · rfl
      · exact absurd (hrep 112 h2) (by omega)
  have h1 : Nat.blt M (Nat.shiftLeft 1 14336) = true := blt_of_bits fun p hp => (hM p hp).1
  have h2 : Nat.beq (Nat.land M pad) 0 = true := by
    rw [Nat.beq_eq]
    exact hz
  unfold canonJ andB
  simp only [h1, h2]

private theorem andB_split {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := andB_true h

private theorem eqRows_enc {X Y : Array V2} (hX : WfA X) (hY : WfA Y) {b : Bool}
    (h : Nat.beq (encR X) (encR Y) = b) : eqRows X Y = b := by
  rw [eqRows_eq hX hY, h]

private theorem wfA_mem {X : Array V2} (h : WfA X) : ∀ x ∈ X, x.wf = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  exact Array.all_eq_true.mp h.2 i hi

private theorem idRows_mul {X : Array V2} (hX : WfA X) : mulRows (idRows ()) X = X := by
  have hW := wf_mulRows wf_idRows hX
  apply eqRows_iff.mp
  cases h : eqRows (mulRows (idRows ()) X) X
  · exact absurd (by rw [rowsMatrix_mulRows, rowsMatrix_idRows, one_mul])
      (rowsMatrix_ne_of_eqRows_false hW.1 hX.1 (wfA_mem hW) (wfA_mem hX) h)
  · rfl

private theorem pow2 {X : Array V2} (hX : WfA X) : powRows X 2 = mulRows X X := by
  change mulRows (mulRows (idRows ()) X) X = _
  rw [idRows_mul hX]

private theorem invsOK_of (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {mats invs : Array (Array V2)} {ms is : List Nat} (hs : mats.size = invs.size)
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k)
    (h : ∀ k < mats.size, Nat.beq (mulJ c rm (getN one ms k) (getN one is k)) one = true) :
    invsOK mats invs = true := by
  unfold invsOK
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨hs, fun k hk => ?_⟩
  rw [List.mem_range] at hk
  have e1 : mats[k]! = mats[k]?.getD (idRows ()) := by
    rw [getElem!_pos mats k hk, Array.getElem?_eq_getElem hk, Option.getD_some]
  have e2 : invs[k]! = invs[k]?.getD (idRows ()) := by
    rw [getElem!_pos invs k (hs ▸ hk), Array.getElem?_eq_getElem (hs ▸ hk), Option.getD_some]
  rw [e1, e2]
  refine eqRows_enc (wf_mulRows (hm k).1 (hi k).1) wf_idRows ?_
  rw [enc_mulRows hK (hm k).1 (hi k).1, (hm k).2, (hi k).2, enc_idRows hK]
  exact h k hk

private theorem locRun_fix {D : MatData} {r : Nat} : ∀ (ws : List (List Int)) (L Li : List Nat),
    locRun D r ws L Li = true → ∀ k < ws.length, Nat.beq (vecJ D.rm r (L.getD k 0)) r = true
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | w :: ws, x :: L, xi :: Li, h, k, hk => by
    change andB (Nat.beq x (wordJ D.c D.rm D.one [D.A, D.B] [D.Ai, D.Bi] w))
      (andB (andB (canonJ D.pad xi) (Nat.beq (mulJ D.c D.rm x xi) D.one))
        (andB (Nat.beq (vecJ D.rm r x) r) (locRun D r ws L Li))) = true at h
    obtain ⟨-, h⟩ := andB_true h
    obtain ⟨-, h⟩ := andB_true h
    obtain ⟨h3, h⟩ := andB_true h
    rcases k with _ | k
    · exact h3
    · rw [List.getD_cons_succ]
      exact locRun_fix ws L Li h k (by simpa using hk)

theorem matFacts_sound (D : MatData) (_hA : seedA = String.ofList D.LA)
    (_hB : seedB = String.ofList D.LB) (_hc : D.consts = true) (_hs : D.seeds = true)
    (_hi : D.invs = true) (_hl : D.loc = true) (_hp : D.pows = true) (_hj : D.conj = true)
    (_hf : D.form = true) : MatFacts := by
  have hK : Consts D.c D.rm D.one D.pad D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6 := _hc
  obtain ⟨hm, hi, hlm, hli⟩ := gens_enc D _hA _hB _hc _hs _hi _hl
  obtain ⟨hlL, hlLi, hkw⟩ := locRun_sound (localWords ()) D.L D.Li _hl
  have hfix := locRun_fix (localWords ()) D.L D.Li _hl
  have hId : WfA (idRows ()) ∧ encR (idRows ()) = D.one := ⟨wf_idRows, enc_idRows hK⟩
  have hA : WfA (rowsA ()) ∧ encR (rowsA ()) = D.A := by simpa [baseMats, getN_eq] using hm 0
  have hB : WfA (rowsB ()) ∧ encR (rowsB ()) = D.B := by simpa [baseMats, getN_eq] using hm 1
  obtain ⟨hcan, hmul⟩ := andB_true _hi
  obtain ⟨hmA, hmB⟩ := andB_true hmul
  have hlen : (localWords ()).length = 3 := rfl
  rw [MatData.pows, strictB_eq] at _hp
  obtain ⟨p1, _hp⟩ := andB_true _hp
  obtain ⟨p2, _hp⟩ := andB_true _hp
  obtain ⟨p3, _hp⟩ := andB_true _hp
  obtain ⟨p4, _hp⟩ := andB_true _hp
  obtain ⟨p5, p6⟩ := andB_true _hp
  have hAB : WfA (mulRows (rowsA ()) (rowsB ())) ∧
      encR (mulRows (rowsA ()) (rowsB ())) = mulJ D.c D.rm D.A D.B :=
    ⟨wf_mulRows hA.1 hB.1, by rw [enc_mulRows hK hA.1 hB.1, hA.2, hB.2]⟩
  rw [MatData.conj, strictB_eq] at _hj
  obtain ⟨j1, _hj⟩ := andB_true _hj
  obtain ⟨j2, _hj⟩ := andB_true _hj
  obtain ⟨j2a, j2b⟩ := andB_true j2
  obtain ⟨j3, j4⟩ := andB_true _hj
  obtain ⟨wC, nC⟩ := enc_wordRows hK hm hi (conjWord ())
  have hC : WfA (conjRows ()) ∧ encR (conjRows ()) = D.C :=
    ⟨wC, by unfold conjRows; rw [nC]; exact (Nat.eq_of_beq_eq_true j1).symm⟩
  have hCi := invRows_enc hK hC.1 j2a (by rw [hC.2]; exact j2b)
  have hz : WfA (zRows ()) ∧ encR (zRows ()) = mulJ D.c D.rm (mulJ D.c D.rm
      (mulJ D.c D.rm D.A D.Ci) (mulJ D.c D.rm D.A D.B)) D.C := by
    have w1 := wf_mulRows hA.1 hCi.1
    have w2 := wf_mulRows w1 hAB.1
    refine ⟨wf_mulRows w2 hC.1, ?_⟩
    change encR (mulRows (mulRows (mulRows (rowsA ()) (invRows (conjRows ())))
      (mulRows (rowsA ()) (rowsB ()))) (conjRows ())) = _
    rw [enc_mulRows hK w2 hC.1, enc_mulRows hK w1 hAB.1, enc_mulRows hK hA.1 hCi.1, hA.2, hCi.2,
      hAB.2, hC.2]
  obtain ⟨f1, f2⟩ := andB_true _hf
  obtain ⟨f2, f3⟩ := andB_true f2
  have hFc : canonJ D.pad D.F = true := by
    rw [← Nat.eq_of_beq_eq_true f2]
    exact canonJ_of_canB hK (canB_mulJ hK _ _)
  have hF := packOK_sound hK f1 hFc
  have hform : ∀ {X : Array V2} {M : Nat}, WfA X → encR X = M →
      Nat.beq (mulJ D.c D.rm (mulJ D.c D.rm M D.F) (trJ D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6 M))
        D.F = true →
      eqRows (mulRows (mulRows X formRows) (transposeRows X)) formRows = true := by
    intro X M hX hM h
    have w1 := wf_mulRows hX hF.1
    refine eqRows_enc (wf_mulRows w1 (wf_transposeRows X)) hF.1 ?_
    rw [enc_mulRows hK w1 (wf_transposeRows X), enc_mulRows hK hX hF.1,
      enc_transposeRows hK hX, hM, hF.2]
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine invsOK_of hK (by simp [baseInvs]) hm hi fun k hk => ?_
    have hk2 : k < 2 := by simpa [baseMats] using hk
    rcases k with _ | _ | k
    · exact hmA
    · exact hmB
    · omega
  · refine invsOK_of hK (by simp [locInvs]) hlm hli fun k hk => ?_
    have hk3 : k < 3 := by simpa [locMats, hlen] using hk
    rw [getN_eq, getN_eq, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    have := (hkw k (by omega)).2.2
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
  · simp only [locMats, Array.size_map, List.size_toArray]
    rfl
  · simp only [stabMats, Array.size_map, List.size_toArray]
    rfl
  · rw [Array.all_eq_true]
    intro k hk
    have hk3 : k < 3 := by simpa [locMats, hlen] using hk
    have hM := hlm k
    rw [Array.getElem?_eq_getElem hk, Option.getD_some, getN_eq,
      List.getD_eq_getElem _ _ (by omega)] at hM
    have hr : rootV.wf = true := by decide
    rw [beq_v2N, v2N_frApply hK hM.1 hr, hM.2]
    have := hfix k (by omega)
    rwa [List.getD_eq_getElem _ _ (by omega)] at this
  · refine eqRows_enc (wf_powRows hA.1 2) wf_idRows ?_
    rw [pow2 hA.1, enc_mulRows hK hA.1 hA.1, hA.2, enc_idRows hK]
    exact p1
  · exact eqRows_enc hA.1 wf_idRows (by rw [hA.2, enc_idRows hK]; exact beq_false p2)
  · refine eqRows_enc (wf_powRows hB.1 4) wf_idRows ?_
    rw [enc_powRows hK hB.1 4, hB.2, enc_idRows hK]
    exact p3
  · refine eqRows_enc (wf_powRows hB.1 2) wf_idRows ?_
    rw [pow2 hB.1, enc_mulRows hK hB.1 hB.1, hB.2, enc_idRows hK]
    exact beq_false p4
  · refine eqRows_enc (wf_powRows hAB.1 37) wf_idRows ?_
    rw [enc_powRows hK hAB.1 37, hAB.2, enc_idRows hK]
    exact p5
  · exact eqRows_enc hAB.1 wf_idRows (by rw [hAB.2, enc_idRows hK]; exact beq_false p6)
  · refine eqRows_enc (wf_mulRows hC.1 hCi.1) wf_idRows ?_
    rw [enc_mulRows hK hC.1 hCi.1, hC.2, hCi.2, enc_idRows hK]
    exact j2b
  · refine eqRows_enc (wf_powRows hz.1 43) wf_idRows ?_
    rw [enc_powRows hK hz.1 43, hz.2, enc_idRows hK]
    exact j3
  · exact eqRows_enc hz.1 wf_idRows (by rw [hz.2, enc_idRows hK]; exact beq_false j4)
  · exact hform hA.1 hA.2 f2
  · exact hform hB.1 hB.2 f3

end CFSG.KC.J4Q

end
