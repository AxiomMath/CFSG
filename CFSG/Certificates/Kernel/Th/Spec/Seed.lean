module

public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.SeedS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

private theorem andB_true_th {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem strictB_eq_th (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem decRun_cons (M : ℕ) (ch : Char) (cs : List Char) (ph i j acc : ℕ) :
    decRun M (ch :: cs) ph i j acc =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (decRun M cs 0 i j acc) (decRun M cs 1 i j acc)
          (Nat.beq ch.toNat 10))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (decRun M cs 1 i (j + 1) (acc + (ent2 ch.toNat <<< j)))
              (andB (Nat.beq (row256 M i) (acc + (ent2 ch.toNat <<< j)))
                (decRun M cs 1 (i + 1) 0 0))
              (Nat.beq (j + 1) 248))
            (decRun M cs 1 i j acc) (Nat.ble 248 i))
          (decRun M cs 1 i j acc) (isWs ch.toNat))
        (Nat.beq ph 1) := by
  unfold decRun
  simp only [strictB_eq_th]
  try rfl

private theorem row256_eq (M r : ℕ) : row256 M r = (M >>> (256 * r)) % 2 ^ 256 := by
  unfold row256
  change (M >>> (256 * r)) &&& (2 ^ 256 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private noncomputable def dgTh (c : Char) : ℕ :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

private noncomputable def entsTh (B : List Char) : List ℕ :=
  (B.filter fun c => !wsChar c).map dgTh

private noncomputable def gE (E : List ℕ) (i j : ℕ) : Bool := (E[i * 248 + j]?.getD 0) % 2 == 1

private def rowBitsTh (m : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range m).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

private theorem char_beq_th (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Char.ext (UInt32.toNat_inj.mp h)

private theorem char_le_th (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat :=
  UInt32.le_iff_toNat_le

private theorem orB_eq_th (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

private theorem andB_eq_th (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem nbeq_th (x k : ℕ) : Nat.beq x k = (x == k) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq])

private theorem isWs_eq_th (c : Char) : isWs c.toNat = wsChar c := by
  unfold isWs wsChar
  rw [char_beq_th, char_beq_th, char_beq_th, char_beq_th]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  simp only [orB_eq_th, nbeq_th, Bool.or_assoc]

private theorem ent2_eq_th (c : Char) : ent2 c.toNat = dgTh c % 2 := by
  unfold ent2 dgTh
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  rw [e0, andB_eq_th]
  have hd : ('0' ≤ c && c ≤ '9') = (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, char_le_th, e0, e9]
  rw [hd]
  cases Nat.ble 48 c.toNat <;> cases Nat.ble c.toNat 57 <;> simp [Nat.and_one_is_mod]

private theorem rowBitsTh_succ (m : ℕ) (f : ℕ → Bool) :
    rowBitsTh (m + 1) f = rowBitsTh m f ||| (if f m then 1 <<< m else 0) := by
  unfold rowBitsTh
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split <;> simp

private theorem rowBitsTh_congr {f f' : ℕ → Bool} : ∀ m, (∀ j < m, f j = f' j) →
    rowBitsTh m f = rowBitsTh m f'
  | 0, _ => rfl
  | m + 1, h => by
    rw [rowBitsTh_succ, rowBitsTh_succ, rowBitsTh_congr m (fun j hj => h j (by omega)),
      h m (by omega)]

private theorem rowBitsTh_lt (f : ℕ → Bool) : ∀ m, rowBitsTh m f < 2 ^ m
  | 0 => by
    unfold rowBitsTh
    simp
  | m + 1 => by
    rw [rowBitsTh_succ]
    have h1 : rowBitsTh m f < 2 ^ (m + 1) :=
      Nat.lt_of_lt_of_le (rowBitsTh_lt f m) (Nat.pow_le_pow_right (by omega) (by omega))
    split
    · rw [Nat.one_shiftLeft]
      exact Nat.or_lt_two_pow h1 (Nat.pow_lt_pow_right (by omega) (by omega))
    · rw [Nat.or_zero]
      exact h1

private theorem rowBitsTh_tail {f : ℕ → Bool} {j : ℕ} : ∀ d,
    (∀ j', j ≤ j' → j' < j + d → f j' = false) → rowBitsTh (j + d) f = rowBitsTh j f
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, rowBitsTh_succ, rowBitsTh_tail d (fun j' h1 h2 => h j' h1 (by omega)),
      h (j + d) (by omega) (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero]

private theorem testBit_rowBitsTh (f : ℕ → Bool) (j : ℕ) : ∀ m,
    (rowBitsTh m f).testBit j = (decide (j < m) && f j)
  | 0 => by simp [rowBitsTh]
  | m + 1 => by
    rw [rowBitsTh_succ, Nat.testBit_or, testBit_rowBitsTh f j m]
    by_cases e : j = m
    · subst e
      by_cases hf : f j
      · simp [hf, Nat.one_shiftLeft, Nat.testBit_two_pow]
      · simp [hf]
    · have e' : j < m + 1 ↔ j < m := by omega
      by_cases hf : f m
      · simp [hf, e', Nat.one_shiftLeft, Nat.testBit_two_pow, e, eq_comm]
      · simp [hf, e']

private theorem gE_past {E : List ℕ} {i j : ℕ} (h : E.length ≤ i * 248 + j) :
    gE E i j = false := by
  unfold gE
  rw [List.getElem?_eq_none h]
  rfl

private theorem getD_append_left_th {pre X : List ℕ} {n : ℕ} (h : n < pre.length) :
    (pre ++ X)[n]?.getD 0 = pre[n]?.getD 0 := by
  rw [List.getElem?_append_left h]

private theorem bit_shl_th (x m : ℕ) : (x % 2) <<< m = if (x % 2 == 1) then 1 <<< m else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h]
  · simp
  · rfl


private theorem dec_body (M : ℕ) : ∀ (B : List Char) (i j acc : ℕ) (pre : List ℕ),
    (i < 248 → pre.length = 248 * i + j ∧ j < 248 ∧ acc = rowBitsTh j (gE pre i)) →
    (248 ≤ i → i = 248 ∧ acc = 0) →
    decRun M B 1 i j acc = true →
    M >>> (256 * 248) = 0 ∧
      ∀ r < 248, i ≤ r → row256 M r = rowBitsTh 248 (gE (pre ++ entsTh B) r)
  | [], i, j, acc, pre, h1, h2, h => by
    have hM : M >>> (256 * i) = acc := Nat.eq_of_beq_eq_true h
    have he : pre ++ entsTh [] = pre := by simp [entsTh]
    rw [he]
    by_cases hi : i < 248
    · obtain ⟨hl, hj, hacc⟩ := h1 hi
      have hlt : acc < 2 ^ 248 := by
        rw [hacc]
        exact Nat.lt_of_lt_of_le (rowBitsTh_lt _ j) (Nat.pow_le_pow_right (by omega) (by omega))
      have hshift : ∀ d, 0 < d → acc >>> (256 * d) = 0 := fun d hd =>
        Nat.shiftRight_eq_zero _ _
          (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
      have hMr : ∀ r, i ≤ r → M >>> (256 * r) = acc >>> (256 * (r - i)) := fun r hr => by
        rw [← hM, ← Nat.shiftRight_add]
        congr 1
        rw [← Nat.mul_add]
        congr 1
        omega
      refine ⟨by rw [hMr 248 (by omega), hshift _ (by omega)], fun r hr1 hr2 => ?_⟩
      rw [row256_eq, hMr r hr2]
      by_cases hri : r = i
      · subst hri
        rw [Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))),
          hacc]
        have e : 248 = j + (248 - j) := by omega
        rw [e, rowBitsTh_tail (248 - j) fun j' h3 _ => gE_past (by rw [hl]; omega)]
      · rw [hshift _ (by omega), Nat.zero_mod]
        have e : 248 = 0 + 248 := rfl
        rw [e, rowBitsTh_tail 248 fun j' _ _ => gE_past (by rw [hl]; omega)]
        rfl
    · obtain ⟨hi', hacc⟩ := h2 (by omega)
      subst hi' hacc
      exact ⟨hM, fun r hr1 hr2 => absurd hr2 (by omega)⟩
  | ch :: B, i, j, acc, pre, h1, h2, h => by
    rw [decRun_cons] at h
    have e1 : Nat.beq 1 1 = true := rfl
    rw [e1] at h
    dsimp only at h
    by_cases hws : wsChar ch = true
    · rw [isWs_eq_th, hws] at h
      dsimp only at h
      have he : entsTh (ch :: B) = entsTh B := by
        simp [entsTh, hws]
      rw [he]
      exact dec_body M B i j acc pre h1 h2 h
    · have hws' : wsChar ch = false := by simpa using hws
      rw [isWs_eq_th, hws'] at h
      dsimp only at h
      have he : entsTh (ch :: B) = dgTh ch :: entsTh B := by
        simp [entsTh, hws']
      have ha : pre ++ dgTh ch :: entsTh B = (pre ++ [dgTh ch]) ++ entsTh B := by simp
      rw [he, ha]
      cases hb : Nat.ble 248 i <;> rw [hb] at h <;> dsimp only at h
      · have hi : i < 248 := by
          apply Nat.lt_of_not_le
          intro h'
          rw [Nat.ble_eq_true_of_le h'] at hb
          exact Bool.noConfusion hb
        obtain ⟨hl, hj, hacc⟩ := h1 hi
        have hl' : (pre ++ [dgTh ch]).length = 248 * i + (j + 1) := by simp [hl]; omega
        have hr : acc + (ent2 ch.toNat <<< j) = rowBitsTh (j + 1) (gE (pre ++ [dgTh ch]) i) := by
          rw [hacc, ent2_eq_th, rowBitsTh_succ]
          have e1 : ∀ j' < j, gE pre i j' = gE (pre ++ [dgTh ch]) i j' := by
            intro j' hj'
            unfold gE
            rw [getD_append_left_th (by rw [hl]; omega)]
          rw [rowBitsTh_congr _ e1]
          have e2 : gE (pre ++ [dgTh ch]) i j = (dgTh ch % 2 == 1) := by
            unfold gE
            have : i * 248 + j = pre.length := by rw [hl]; omega
            rw [this, List.getElem?_concat_length]
            rfl
          rw [e2, bit_shl_th]
          split
          · rw [Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt (rowBitsTh_lt _ j), Nat.or_comm]
          · rw [Nat.add_zero, Nat.or_zero]
        cases hlast : Nat.beq (j + 1) 248 <;> rw [hlast] at h <;> dsimp only at h
        · have hj1 : j + 1 ≠ 248 := fun e => by
            rw [e, Nat.beq_refl] at hlast
            exact Bool.noConfusion hlast
          exact dec_body M B i (j + 1) _ (pre ++ [dgTh ch]) (fun _ => ⟨hl', by omega, hr⟩)
            (fun h' => absurd h' (by omega)) h
        · have hj1 : j + 1 = 248 := Nat.eq_of_beq_eq_true hlast
          obtain ⟨hrow, hrest⟩ := andB_true_th h
          have hrow' : row256 M i = rowBitsTh 248 (gE (pre ++ [dgTh ch]) i) := by
            rw [Nat.eq_of_beq_eq_true hrow, hr, hj1]
          have ih := dec_body M B (i + 1) 0 0 (pre ++ [dgTh ch])
            (fun _ => ⟨by rw [hl']; omega, by omega, rfl⟩) (fun _ => ⟨by omega, rfl⟩) hrest
          refine ⟨ih.1, fun r hr1 hr2 => ?_⟩
          by_cases hri : r = i
          · subst hri
            rw [hrow']
            apply rowBitsTh_congr
            intro j' hj'
            unfold gE
            rw [getD_append_left_th (pre := pre ++ [dgTh ch]) (X := entsTh B)
              (by rw [hl']; omega)]
          · exact ih.2 r hr1 (by omega)
      · obtain ⟨hi, hacc⟩ := h2 (Nat.le_of_ble_eq_true hb)
        exact dec_body M B i j acc (pre ++ [dgTh ch]) (fun h' => absurd h' (by omega))
          (fun _ => ⟨hi, hacc⟩) h


private theorem dec_header (M : ℕ) : ∀ cs : List Char, decRun M cs 0 0 0 0 = true →
    decRun M ((cs.dropWhile (· != '\n')).drop 1) 1 0 0 0 = true
  | [], h => h
  | ch :: cs, h => by
    rw [decRun_cons] at h
    have e0 : Nat.beq 0 1 = false := rfl
    rw [e0] at h
    dsimp only at h
    by_cases hc : ch = '\n'
    · subst hc
      exact h
    · have h10 : Nat.beq (Char.toNat ch) 10 = false := by
        cases hb : Nat.beq (Char.toNat ch) 10
        · rfl
        · exfalso
          apply hc
          have := Nat.eq_of_beq_eq_true hb
          exact Char.ext (UInt32.toNat_inj.mp (by simpa using this))
      rw [h10] at h
      dsimp only at h
      have hne : (ch != '\n') = true := by simpa using hc
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact dec_header M cs h

theorem rowsMatrix_rowsOf_apply (s : String) (i j : Fin 248) :
    rowsMatrix (rowsOf s) i j =
      if ((decodeEntries s)[i.val * 248 + j.val]?.getD 0) % 2 == 1 then 1 else 0 := by
  rw [rowsMatrix_apply]
  unfold rowsOf
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  unfold rowOfEntries
  rw [V4.toVec_ofFn, List.getElem?_toArray]

theorem decOK_sound {M : ℕ} {l : List Char} (h : decOK M l = true) :
    InLayout M ∧ pkMat M = rowsMatrix (rowsOf (String.ofList l)) := by
  obtain ⟨hM, hrows⟩ := dec_body M _ 0 0 0 [] (fun _ => ⟨rfl, by omega, rfl⟩)
    (fun h => absurd h (by omega)) (dec_header M l h)
  have hdec : decodeEntries (String.ofList l) =
      entsTh ((l.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries entsTh dgTh
    rw [String.toList_ofList]
  have hbit : ∀ p, M.testBit p = (decide (p % 256 < 248 ∧ p / 256 < 248) &&
      gE (decodeEntries (String.ofList l)) (p / 256) (p % 256)) := by
    intro p
    by_cases hp : p / 256 < 248
    · have hr := hrows (p / 256) hp (Nat.zero_le _)
      rw [List.nil_append, ← hdec] at hr
      have h1 := congrArg (fun x => x.testBit (p % 256)) hr
      simp only [row256_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
        testBit_rowBitsTh] at h1
      have e : 256 * (p / 256) + p % 256 = p := by omega
      have hm : p % 256 < 256 := Nat.mod_lt _ (by omega)
      rw [e] at h1
      simp only [hm, decide_true, Bool.true_and] at h1
      rw [h1]
      simp [hp]
    · have h0 : (M >>> (256 * 248)).testBit (p - 256 * 248) = false := by
        rw [hM]
        exact Nat.zero_testBit _
      rw [Nat.testBit_shiftRight] at h0
      have e : 256 * 248 + (p - 256 * 248) = p := by omega
      rw [e] at h0
      rw [h0]
      simp [hp]
  refine ⟨fun b hb => ?_, ?_⟩
  · rw [hbit, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact hb.1
  · ext i j
    have hi := i.isLt
    have hj := j.isLt
    rw [pkMat_apply, rowsMatrix_rowsOf_apply, hbit]
    have e1 : (256 * i.val + j.val) % 256 = j.val := by omega
    have e2 : (256 * i.val + j.val) / 256 = i.val := by omega
    rw [e1, e2, show decide (j.val < 248 ∧ i.val < 248) = true by simp [hi, hj], Bool.true_and]
    rfl


private theorem or_eq_add_th {x i y : ℕ} (hx : x < 2 ^ i) : 2 ^ i * y ||| x = 2 ^ i * y + x :=
  (Nat.two_pow_add_eq_or_of_lt hx y).symm

private theorem v4Nat_eq (v : V4) : v4Nat v = v.toNat := by
  have ha := UInt64.toNat_lt v.w0
  have hb := UInt64.toNat_lt v.w1
  have hc := UInt64.toNat_lt v.w2
  have hd := UInt64.toNat_lt v.w3
  unfold v4Nat V4.toNat
  change v.w0.toNat ||| (v.w1.toNat <<< 64 ||| (v.w2.toNat <<< 128 ||| v.w3.toNat <<< 192)) = _
  simp only [Nat.shiftLeft_eq]
  have e1 : v.w2.toNat * 2 ^ 128 ||| v.w3.toNat * 2 ^ 192 =
      2 ^ 192 * v.w3.toNat + v.w2.toNat * 2 ^ 128 := by
    rw [Nat.or_comm, Nat.mul_comm v.w3.toNat, or_eq_add_th (by omega)]
  have e2 : v.w1.toNat * 2 ^ 64 ||| (2 ^ 192 * v.w3.toNat + v.w2.toNat * 2 ^ 128) =
      2 ^ 128 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) + v.w1.toNat * 2 ^ 64 := by
    rw [Nat.or_comm, show 2 ^ 192 * v.w3.toNat + v.w2.toNat * 2 ^ 128 =
      2 ^ 128 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) by omega, or_eq_add_th (by omega)]
  have e3 : v.w0.toNat ||| (2 ^ 128 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) +
      v.w1.toNat * 2 ^ 64) = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) +
      v.w1.toNat) + v.w0.toNat := by
    rw [Nat.or_comm, show 2 ^ 128 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) + v.w1.toNat * 2 ^ 64 =
      2 ^ 64 * (2 ^ 64 * (2 ^ 64 * v.w3.toNat + v.w2.toNat) + v.w1.toNat) by omega,
      or_eq_add_th ha]
  rw [e1, e2, e3]
  omega

private theorem testBit_v4Nat (v : V4) (j : ℕ) :
    (v4Nat v).testBit j = (decide (j < 256) && v.testBit j) := by
  rw [v4Nat_eq]
  by_cases hj : j < 256
  · rw [V4.testBit_toNat v hj]
    simp [hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (V4.toNat_lt v)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hj]

private theorem v4Nat_lt (v : V4) : v4Nat v < 2 ^ 256 := by
  rw [v4Nat_eq]
  exact V4.toNat_lt v

private noncomputable def packRowsTh : List V4 → ℕ → ℕ
  | [], _ => 0
  | v :: l, r => (v4Nat v <<< (256 * r)) ||| packRowsTh l (r + 1)

private theorem packFrom_eq : ∀ (l : List V4) (r : ℕ),
    packFrom l r = packRowsTh l r ||| ((r + l.length) <<< 65536)
  | [], r => by
    change Nat.shiftLeft r 65536 = 0 ||| (r + 0) <<< 65536
    rw [Nat.zero_or]
    rfl
  | v :: l, r => by
    change Nat.lor (Nat.shiftLeft (v4Nat v) (Nat.mul 256 r)) (packFrom l (Nat.succ r)) =
      ((v4Nat v <<< (256 * r)) ||| packRowsTh l (r + 1)) ||| ((r + (l.length + 1)) <<< 65536)
    rw [packFrom_eq l (r + 1), Nat.or_assoc]
    change (v4Nat v <<< (256 * r)) ||| (packRowsTh l (r + 1) ||| ((r + 1 + l.length) <<< 65536)) = _
    rw [show r + (l.length + 1) = r + 1 + l.length by omega]

private theorem testBit_packRowsTh (p : ℕ) : ∀ (l : List V4) (r : ℕ),
    (packRowsTh l r).testBit p =
      (decide (r ≤ p / 256) && (v4Nat (l.getD (p / 256 - r) V4.zero)).testBit (p % 256))
  | [], r => by
    have : v4Nat V4.zero = 0 := by
      rw [v4Nat_eq]
      exact V4.toNat_zero
    simp [packRowsTh, this]
  | v :: l, r => by
    rw [packRowsTh, Nat.testBit_or, testBit_shl_row (v4Nat_lt v) r p,
      testBit_packRowsTh p l (r + 1)]
    by_cases h1 : p / 256 < r
    · simp [h1, show ¬ p / 256 = r by omega, show ¬ r ≤ p / 256 by omega,
        show ¬ r + 1 ≤ p / 256 by omega]
    · by_cases h2 : p / 256 = r
      · simp [h2]
      · have e : p / 256 - r = (p / 256 - (r + 1)) + 1 := by omega
        simp [h2, show r ≤ p / 256 by omega, show r + 1 ≤ p / 256 by omega, e]

theorem packOK_sound {M : ℕ} {l : List V4} (h : packOK M l = true) :
    pkMat M = rowsMatrix l.toArray := by
  have h1 : packFrom l 0 = M ||| (248 <<< 65536) := Nat.eq_of_beq_eq_true h
  rw [packFrom_eq] at h1
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [pkMat_apply, rowsMatrix_apply]
  have h2 := congrArg (fun x => x.testBit (256 * i.val + j.val)) h1
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_packRowsTh] at h2
  have e1 : (256 * i.val + j.val) / 256 = i.val := by omega
  have e2 : (256 * i.val + j.val) % 256 = j.val := by omega
  have e3 : ¬ (256 * i.val + j.val ≥ 65536) := by omega
  rw [e1, e2, Nat.sub_zero, testBit_v4Nat] at h2
  simp only [e3, decide_false, Bool.false_and, Bool.or_false, Nat.zero_le, decide_true,
    Bool.true_and, show j.val < 256 by omega] at h2
  rw [← h2, V4.toVec_apply, List.getElem?_toArray, List.getD_eq_getElem?_getD]


@[expose] def WfRows (X : Array V4) : Prop := X.size = 248 ∧ ∀ x ∈ X, x.wf = true

theorem rowsMatrix_inj {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y)
    (h : rowsMatrix X = rowsMatrix Y) : X = Y := by
  refine Array.ext (hX.1.trans hY.1.symm) fun i h1 h2 => ?_
  have hi : i < 248 := hX.1 ▸ h1
  have h3 := congrFun (congrFun h ⟨i, hi⟩) 
  have h4 : (X[i]?.getD V4.zero).toVec = (Y[i]?.getD V4.zero).toVec := funext h3
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at h4
  exact V4.eq_of_toVec_eq (hX.2 _ (Array.getElem_mem h1)) (hY.2 _ (Array.getElem_mem h2)) h4

theorem eqRows_of_rowsMatrix_eq {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y)
    (h : rowsMatrix X = rowsMatrix Y) : eqRows X Y = true :=
  eqRows_iff.2 (rowsMatrix_inj hX hY h)

theorem wfRows_rowsOf (s : String) : WfRows (rowsOf s) := ⟨rowsOf_size s, rowsOf_wf s⟩

theorem wfRows_transposeRows (X : Array V4) : WfRows (transposeRows X) :=
  ⟨transposeRows_size X, transposeRows_wf X⟩

theorem wfRows_mulRows {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y) :
    WfRows (Native.mulRows X Y) :=
  ⟨(mulRows_size X Y).trans hX.1, mulRows_wf X hY.2⟩

theorem wfRows_idRows : WfRows idRows := ⟨idRows_size, idRows_wf⟩

theorem wfRows_fcRows : WfRows fcRows := by
  refine ⟨by decide +kernel, fun x hx => ?_⟩
  have h : fcRows.toList.all V4.wf = true := by decide +kernel
  exact List.all_eq_true.1 h x (Array.mem_toList_iff.2 hx)

theorem fcRowsList_toArray : fcRowsList.toArray = fcRows := Array.toArray_toList

end CFSG.KC.Th.Spec

end
