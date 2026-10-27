module

public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import Certificates.Data.Kernel.BabyMonster.LatDecode

public section

namespace CFSG.KC.BM.Lat

open CFSG.Monster.B.Dyadic.Native CFSG.KC.BM.B64

@[expose] noncomputable def blockNZ (Bs : List (List Nat)) (i0 c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k ih => orB ih (notB (Nat.beq (Nat.shiftRight (recOf Bs (Nat.add i0 k)) (nat_lit 16))
      (nat_lit 0)))) c

@[expose] noncomputable def nzAll (Bs : List (List Nat)) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih (blockNZ Bs (Nat.mul (nat_lit 64) s)
      (Nat.min (nat_lit 64) (Nat.sub (nat_lit 4371) (Nat.mul (nat_lit 64) s))))) (nat_lit 69)

@[expose] noncomputable def lastLenOK (CH : List (Nat × Nat)) : Bool :=
  Nat.ble (nat_lit 9) (getP CH (nat_lit 43526)).2

end CFSG.KC.BM.Lat

end

namespace CFSG.KC.BM.Lat

open CFSG.Monster.B.Dyadic.Native CFSG.KC.BM.B64

theorem iteT {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem latAndB_true {b c : Bool} (h : andB b c = true) : b = true ∧ c = true := by
  cases b
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem latRecAnd_true {X : Nat → Bool} : ∀ {n : Nat},
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) n = true →
      ∀ i < n, X i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) (n + 1) =
        andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (X i)) n) (X n) := rfl
    obtain ⟨h1, h2⟩ := latAndB_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact latRecAnd_true h1 i hi
    · exact h2

theorem blockNZ_true {Bs : List (List Nat)} {i0 : Nat} : ∀ {c : Nat}, blockNZ Bs i0 c = true →
    ∃ k < c, recOf Bs (i0 + k) >>> 16 ≠ 0
  | 0, h => absurd h Bool.false_ne_true
  | c + 1, h => by
    have e : blockNZ Bs i0 (c + 1) = orB (blockNZ Bs i0 c)
        (notB (Nat.beq (recOf Bs (i0 + c) >>> 16) 0)) := rfl
    rw [e] at h
    cases h1 : blockNZ Bs i0 c
    · rw [h1] at h
      refine ⟨c, Nat.lt_succ_self c, fun h0 => ?_⟩
      rw [h0] at h
      exact absurd h Bool.false_ne_true
    · obtain ⟨k, hk, h2⟩ := blockNZ_true h1
      exact ⟨k, Nat.lt_succ_of_lt hk, h2⟩

theorem ones_eq (k : Nat) : ones k = 2 ^ k - 1 := by
  change 1 <<< k - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_ones (k i : Nat) : (ones k).testBit i = decide (i < k) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_255 (i : Nat) : (255 : Nat).testBit i = decide (i < 8) :=
  Nat.testBit_two_pow_sub_one 8 i

theorem testBit_127 (i : Nat) : (127 : Nat).testBit i = decide (i < 7) :=
  Nat.testBit_two_pow_sub_one 7 i

theorem spread_zero_succ (x n : Nat) :
    spread 0 x (n + 1) = spread 0 x n ||| ((x >>> (7 * n)) &&& 127) <<< (16 * n) := rfl

theorem testBit_spread0 (x : Nat) : ∀ n b, (spread 0 x n).testBit b =
    (decide (b / 16 < n) && decide (b % 16 < 7) && x.testBit (7 * (b / 16) + b % 16))
  | 0, b => by
    change (0 : Nat).testBit b = _
    simp
  | n + 1, b => by
    rw [spread_zero_succ, Nat.testBit_or, testBit_spread0 x n, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_127]
    rcases Nat.lt_trichotomy (b / 16) n with h | h | h
    · have h1 : ¬ (b ≥ 16 * n) := by omega
      have h2 : b / 16 < n + 1 := by omega
      simp [h, h1, h2]
    · have h3 : b - 16 * n = b % 16 := by omega
      have h1 : b ≥ 16 * n := by omega
      subst h
      simp [h1, h3, Bool.and_comm]
    · have h1 : ¬ b / 16 < n := by omega
      have h2 : ¬ b / 16 < n + 1 := by omega
      have h4 : ¬ (b - 16 * n < 7) := by omega
      simp [h1, h2, h4]

theorem spread_succ (d x n : Nat) : spread (d + 1) x n =
    spread d (x &&& ones (7 * (n / 2))) (n / 2) |||
      spread d (x >>> (7 * (n / 2))) (n - n / 2) <<< (16 * (n / 2)) := rfl

theorem spread_eq : ∀ d x n, spread d x n = spread 0 x n
  | 0, _, _ => rfl
  | d + 1, x, n => by
    rw [spread_succ, spread_eq d, spread_eq d]
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_spread0, testBit_spread0, testBit_spread0,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones]
    by_cases h : b / 16 < n / 2
    · have h1 : ¬ (b ≥ 16 * (n / 2)) := by omega
      have h2 : b / 16 < n := by omega
      by_cases h3 : b % 16 < 7
      · have h4 : 7 * (b / 16) + b % 16 < 7 * (n / 2) := by omega
        simp [h, h1, h2, h3, h4]
      · simp [h1, h3]
    · have h1 : b ≥ 16 * (n / 2) := by omega
      have e1 : (b - 16 * (n / 2)) / 16 = b / 16 - n / 2 := by omega
      have e2 : (b - 16 * (n / 2)) % 16 = b % 16 := by omega
      have e3 : 7 * (n / 2) + (7 * (b / 16 - n / 2) + b % 16) = 7 * (b / 16) + b % 16 := by omega
      have e4 : decide (b / 16 - n / 2 < n - n / 2) = decide (b / 16 < n) := by
        simp only [decide_eq_decide]
        omega
      simp [h, h1, e1, e2, e3, e4]

theorem spread_field (x n k : Nat) :
    spread 0 x n / 2 ^ (16 * k) % 65536 = if k < n then (x >>> (7 * k)) % 128 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    testBit_spread0]
  have e1 : t < 16 → (t + 16 * k) / 16 = k := by omega
  have e2 : t < 16 → (t + 16 * k) % 16 = t := by omega
  split
  · rename_i hk
    rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases ht : t < 16
    · simp [ht, e1 ht, e2 ht, hk]
    · have : ¬ t < 7 := by omega
      simp [ht, this]
  · rename_i hk
    by_cases ht : t < 16
    · simp [ht, e1 ht, hk]
    · simp [ht]

theorem rowOK_field {Bs : List (List Nat)} {W b0 i : Nat} (h : rowOK Bs W b0 i = true) (k : Nat) :
    recOf Bs i / 2 ^ (16 * (k + 1)) % 65536 =
      if k < 4370 - i then (W >>> (7 * entBefore i - b0 + 7 * k)) % 128 else 0 := by
  have e : spread 0 ((W >>> (7 * entBefore i - b0)) &&& ones (7 * (4370 - i))) (4370 - i) =
      recOf Bs i >>> 16 := by
    rw [← spread_eq 13]
    exact Nat.eq_of_beq_eq_true h
  have e2 : recOf Bs i / 2 ^ (16 * (k + 1)) = (recOf Bs i >>> 16) / 2 ^ (16 * k) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 2
    omega
  rw [e2, ← e, spread_field]
  split
  · rename_i hk
    apply Nat.eq_of_testBit_eq
    intro t
    rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    simp only [Nat.testBit_shiftRight, Nat.testBit_and, testBit_ones]
    by_cases ht : t < 7
    · have : 7 * k + t < 7 * (4370 - i) := by omega
      simp [ht, this, Nat.add_assoc]
    · simp [ht]
  · rfl

theorem forceB_eq (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem testBit_tripleOf (v s : Nat) (hs : s < 24) :
    (tripleOf v).testBit s = v.testBit (16 - 8 * (s / 8) + s % 8) := by
  change ((v >>> 16) &&& 255 ||| ((((v >>> 8) &&& 255) <<< 8) ||| ((v &&& 255) <<< 16))).testBit s = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    testBit_255]
  by_cases h1 : s < 8
  · have e : 16 - 8 * (s / 8) + s % 8 = 16 + s := by omega
    have h2 : ¬ s ≥ 8 := by omega
    have h3 : ¬ s ≥ 16 := by omega
    simp [h1, h2, h3, e]
  · by_cases h4 : s < 16
    · have e : 16 - 8 * (s / 8) + s % 8 = 8 + (s - 8) := by omega
      have h2 : s ≥ 8 := by omega
      have h3 : ¬ s ≥ 16 := by omega
      have h5 : s - 8 < 8 := by omega
      simp [h1, h2, h3, h5, e]
    · have e : 16 - 8 * (s / 8) + s % 8 = s - 16 := by omega
      have h2 : s ≥ 8 := by omega
      have h3 : s ≥ 16 := by omega
      have h5 : ¬ s - 8 < 8 := by omega
      have h6 : s - 16 < 8 := by omega
      simp [h1, h2, h3, h5, h6, e]

theorem tripleOf_lt (v : Nat) : tripleOf v < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  change ((v >>> 16) &&& 255 ||| ((((v >>> 8) &&& 255) <<< 8) ||| ((v &&& 255) <<< 16))).testBit i = _
  have h1 : ¬ i < 8 := by omega
  have h2 : ¬ i - 8 < 8 := by omega
  have h3 : ¬ i - 16 < 8 := by omega
  simp [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_255, h1, h2, h3]

theorem segDec_succ (N q : Nat) :
    segDec N (q + 1) = segDec N q ||| tripleOf (quadV N q) <<< (24 * q) := by
  have e : segDec N (q + 1) = forceB (segDec N q)
      (fun a => Nat.lor a (Nat.shiftLeft (tripleOf (quadV N q)) (Nat.mul 24 q))) := rfl
  rw [e, forceB_eq]
  rfl

theorem segDec_lt (N : Nat) : ∀ q, segDec N q < 2 ^ (24 * q)
  | 0 => by
    change 0 < _
    exact Nat.two_pow_pos _
  | q + 1 => by
    rw [segDec_succ]
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le (segDec_lt N q) (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [Nat.shiftLeft_eq, show 24 * (q + 1) = 24 + 24 * q by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right (tripleOf_lt _) (Nat.two_pow_pos _)

theorem segDec_testBit_ge (N q b : Nat) (h : 24 * q ≤ b) : (segDec N q).testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (segDec_lt N q) (Nat.pow_le_pow_right (by decide) h))

theorem testBit_segDec (N : Nat) : ∀ q k s, k < q → s < 24 →
    (segDec N q).testBit (24 * k + s) = (tripleOf (quadV N k)).testBit s
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | q + 1, k, s, hk, hs => by
    rw [segDec_succ, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [testBit_segDec N q k s hk hs]
      have : ¬ 24 * k + s ≥ 24 * q := by omega
      simp [this]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (segDec_lt N k) (Nat.pow_le_pow_right
        (by decide) (by omega)))]
      simp

noncomputable def okW : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: t, c => if 0 < c then pieceOK (isNilP t) p && okW t (c - 1) else true

noncomputable def sumW : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | p :: t, c => if 0 < c then segDec p.1 64 ||| sumW t (c - 1) <<< 1536 else 0

noncomputable def winGo (H : Nat) (L : List (Nat × Nat)) : Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun p t ih c m acc => Bool.rec (motive := fun _ => Nat) acc
      (Bool.rec (motive := fun _ => Nat) H
        (forceB (Nat.lor acc (Nat.shiftLeft (segDec p.1 (nat_lit 64)) (Nat.mul (nat_lit 1536) m)))
          (fun a => ih (Nat.sub c (nat_lit 1)) (Nat.succ m) a))
        (pieceOK (isNilP t) p))
      (Nat.blt (nat_lit 0) c))
    L

theorem winOf_eq (L : List (Nat × Nat)) (c : Nat) :
    winOf L c = winGo (Nat.shiftLeft (nat_lit 1) (nat_lit 1073741824)) L c 0 0 := rfl

theorem winGo_eq (H : Nat) : ∀ (L : List (Nat × Nat)) (c m acc : Nat),
    winGo H L c m acc = if okW L c = true then acc ||| sumW L c <<< (1536 * m) else H
  | [], c, m, acc => by
    change acc = _
    simp [okW, sumW]
  | p :: t, c, m, acc => by
    have e : winGo H (p :: t) c m acc = Bool.rec (motive := fun _ => Nat) acc
      (Bool.rec (motive := fun _ => Nat) H
        (forceB (acc ||| segDec p.1 64 <<< (1536 * m)) (fun a => winGo H t (c - 1) (m + 1) a))
        (pieceOK (isNilP t) p)) (Nat.blt 0 c) := rfl
    rw [e, forceB_eq]
    by_cases hc : 0 < c
    · have hb : Nat.blt 0 c = true := by
        cases c with
        | zero => exact absurd hc (Nat.lt_irrefl 0)
        | succ c => rfl
      rw [hb]
      cases hp : pieceOK (isNilP t) p
      · simp [okW, hc, hp]
      · simp only [okW, sumW, hc, hp, ↓reduceIte, Bool.true_and]
        rw [winGo_eq H t]
        split
        · rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc,
            show 1536 + 1536 * m = 1536 * (m + 1) by omega]
        · rfl
    · obtain rfl : c = 0 := by omega
      change acc = _
      simp [okW, sumW]

theorem testBit_sumW : ∀ (L : List (Nat × Nat)) (c b : Nat), b / 1536 < c → b / 1536 < L.length →
    (sumW L c).testBit b = (segDec (L.getD (b / 1536) (0, 0)).1 64).testBit (b % 1536)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | p :: t, c, b, hc, hl => by
    have hc0 : 0 < c := by omega
    simp only [sumW, hc0, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hb : b < 1536
    · have e1 : b / 1536 = 0 := by omega
      have e2 : b % 1536 = b := by omega
      have : ¬ b ≥ 1536 := by omega
      simp [e1, e2, this]
    · have e1 : b / 1536 = (b - 1536) / 1536 + 1 := by omega
      have e2 : b % 1536 = (b - 1536) % 1536 := by omega
      rw [segDec_testBit_ge _ 64 b (by omega)]
      rw [testBit_sumW t (c - 1) (b - 1536) (by omega) (by simp at hl; omega), e1, e2]
      have : b ≥ 1536 := by omega
      simp [this]

theorem dropP_eq : ∀ (L : List (Nat × Nat)) (k : Nat), dropP L k = L.drop k
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => dropP_eq L k

theorem getP_eq (L : List (Nat × Nat)) (k : Nat) : getP L k = L.getD k (0, 0) := by
  change List.rec (motive := fun _ => Nat × Nat) (0, 0) (fun p _ _ => p) (dropP L k) = _
  rw [dropP_eq]
  induction L generalizing k with
  | nil => cases k <;> rfl
  | cons p L ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem lenP_eq : ∀ (L : List (Nat × Nat)), lenP L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenP_eq L)

theorem isNilP_eq (L : List (Nat × Nat)) : isNilP L = L.isEmpty := by
  cases L <;> rfl

theorem getD_drop {α : Type} (L : List α) (n m : Nat) (d : α) :
    (L.drop n).getD m d = L.getD (n + m) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem inR_true {lo hi c : Nat} (h : inR lo hi c = true) : lo ≤ c ∧ c ≤ hi := by
  obtain ⟨h1, h2⟩ := latAndB_true h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩

theorem isB64_ok {c : Nat} (h : isB64 c = true) : c < 128 ∧ c ≠ 10 := by
  have e : isB64 c = (inR 65 90 c || inR 97 122 c || inR 48 57 c || Nat.beq c 43 ||
      Nat.beq c 47 || Nat.beq c 61) := by
    unfold isB64
    cases inR 65 90 c <;> cases inR 97 122 c <;> cases inR 48 57 c <;> cases Nat.beq c 43 <;>
      cases Nat.beq c 47 <;> rfl
  rw [e] at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · have := inR_true h
    omega
  · have := inR_true h
    omega
  · have := inR_true h
    omega
  · have := Nat.eq_of_beq_eq_true h
    omega
  · have := Nat.eq_of_beq_eq_true h
    omega
  · have := Nat.eq_of_beq_eq_true h
    omega

theorem pieceOK_spec {last : Bool} {p : Nat × Nat} (h : pieceOK last p = true) :
    (last = false → p.2 = 256) ∧ p.2 ≤ 256 ∧ ∀ k < p.2, isB64 (chAt p.1 k) = true ∨
      (chAt p.1 k = 10 ∧ k + 1 = p.2 ∧ last = true) := by
  obtain ⟨h1, h2⟩ := latAndB_true h
  refine ⟨fun hl => ?_, ?_, fun k hk => ?_⟩
  · subst hl
    exact Nat.eq_of_beq_eq_true h1
  · cases last
    · exact Nat.le_of_eq (Nat.eq_of_beq_eq_true h1)
    · exact Nat.le_of_ble_eq_true h1
  · have h3 := latRecAnd_true h2 k hk
    cases hb : isB64 (chAt p.1 k)
    · rw [hb] at h3
      obtain ⟨h4, h5⟩ := latAndB_true h3
      obtain ⟨h5, h6⟩ := latAndB_true h5
      exact Or.inr ⟨Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, h6⟩
    · exact Or.inl rfl

theorem chAt_succ (N k : Nat) : chAt (Nat.shiftRight N 8) k = chAt N (k + 1) := by
  change (N >>> 8 >>> (8 * k)) &&& 255 = (N >>> (8 * (k + 1))) &&& 255
  rw [← Nat.shiftRight_add]
  congr 2
  omega

theorem chAt_lt (N k : Nat) : chAt N k < 256 := by
  change (N >>> (8 * k)) &&& 255 < 256
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem decChunkC_eq : ∀ (len N : Nat) (t : List Char),
    CFSG.KC.YModel.decChunkC len N t = (List.range len).map (fun k => Char.ofNat (chAt N k)) ++ t
  | 0, _, _ => rfl
  | len + 1, N, t => by
    have e : CFSG.KC.YModel.decChunkC (len + 1) N t =
        Char.ofNat (Nat.land N 255) :: CFSG.KC.YModel.decChunkC len (Nat.shiftRight N 8) t := rfl
    rw [e, decChunkC_eq len, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
    refine List.cons_eq_cons.2 ⟨rfl, congrArg (· ++ t) (List.map_congr_left fun k _ => ?_)⟩
    rw [Function.comp_apply, chAt_succ]

theorem utf8_ascii : ∀ n < 128, String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  decide +kernel

theorem flatMap_ascii (g : Nat → Nat) : ∀ (L : List Nat),
    (∀ k ∈ L, g k < 128) →
      (L.map fun k => Char.ofNat (g k)).flatMap String.utf8EncodeChar =
        L.map fun k => UInt8.ofNat (g k)
  | [], _ => rfl
  | k :: L, h => by
    rw [List.map_cons, List.flatMap_cons, utf8_ascii _ (h k List.mem_cons_self),
      flatMap_ascii g L (fun k' hk => h k' (List.mem_cons_of_mem _ hk)), List.map_cons]
    rfl

theorem byteArray_get! (b : ByteArray) (i : Nat) : b.get! i = b.data[i]! := by
  cases b
  rfl

noncomputable def codes : List (Nat × Nat) → List Nat
  | [] => []
  | p :: L => (List.range p.2).map (chAt p.1) ++ codes L

theorem charsOf_eq : ∀ (L : List (Nat × Nat)), CFSG.KC.YModel.charsOf L = (codes L).map Char.ofNat
  | [] => rfl
  | (N, len) :: L => by
    change CFSG.KC.YModel.decChunkC len N (CFSG.KC.YModel.charsOf L) = _
    rw [decChunkC_eq, charsOf_eq L, codes, List.map_append, List.map_map]
    rfl

theorem toUTF8_eq (L : List (Nat × Nat)) (h : ∀ c ∈ codes L, c < 128) :
    (String.ofList (CFSG.KC.YModel.charsOf L)).toUTF8 = ((codes L).map UInt8.ofNat).toByteArray := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, charsOf_eq]
  unfold List.utf8Encode
  have := flatMap_ascii (fun k => k) (codes L) h
  exact congrArg List.toByteArray this

theorem codes_get : ∀ (ps : List (Nat × Nat)) (m c : Nat),
    (∀ m' < m, (ps.getD m' (0, 0)).2 = 256) → m < ps.length → c < (ps.getD m (0, 0)).2 →
      (codes ps)[256 * m + c]? = some (chAt (ps.getD m (0, 0)).1 c)
  | [], _, _, _, hm, _ => absurd hm (Nat.not_lt_zero _)
  | p :: t, 0, c, _, _, hc => by
    simp only [List.getD_cons_zero] at hc ⊢
    rw [codes, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by simpa using hc),
      List.getElem?_map, List.getElem?_range hc]
    rfl
  | p :: t, m + 1, c, h256, hm, hc => by
    have hp : p.2 = 256 := h256 0 (Nat.succ_pos m)
    simp only [List.getD_cons_succ] at hc ⊢
    rw [codes, List.getElem?_append_right (by simp [hp]; omega)]
    simp only [List.length_map, List.length_range, hp]
    rw [show 256 * (m + 1) + c - 256 = 256 * m + c by omega]
    exact codes_get t m c (fun m' hm' => by simpa using h256 (m' + 1) (by omega))
      (by simpa using hm) hc

theorem forIn_loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

theorem forIn_list_yield {α β : Type} (g : α → β → β) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g a b)) :
    ∀ (l : List α) (init : β), forIn (m := Id) l init f = l.foldl (fun b a => g a b) init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact forIn_list_yield g f hf l (g a init)

theorem bget (b : ByteArray) (j : Nat) : b.get! j = (b.data[j]?).getD 0 := by
  cases b
  simp only [ByteArray.get!, getElem!_def]
  split <;> simp_all <;> rfl

def scanNL (b : ByteArray) (k : Nat) : Nat :=
  forIn (m := Id) Lean.Loop.mk k (fun _ k =>
    if (k < b.size && b.get! k != 10) = true then pure (ForInStep.yield (k + 1))
    else pure (ForInStep.done k))

theorem lineBreakOf_eq (t : String) : lineBreakOf t = scanNL t.toUTF8 0 := rfl

theorem scanNL_unfold (b : ByteArray) (k : Nat) :
    scanNL b k = if (k < b.size && b.get! k != 10) = true then scanNL b (k + 1) else k := by
  unfold scanNL
  rw [forIn_loop_unfold]
  by_cases h : (k < b.size && b.get! k != 10) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h]
    rfl

theorem scanNL_exact (b : ByteArray) (e : Nat) (he : e < b.size) (h10 : b.get! e = 10) :
    ∀ n k, e - k = n → k ≤ e → (∀ k', k ≤ k' → k' < e → b.get! k' ≠ 10) → scanNL b k = e
  | 0, k, hn, hk, _ => by
    obtain rfl : k = e := by omega
    rw [scanNL_unfold, iteF (by simp [h10])]
  | n + 1, k, hn, hk, h => by
    rw [scanNL_unfold, iteT (by simp [show k < b.size by omega, h k (Nat.le_refl k) (by omega)])]
    exact scanNL_exact b e he h10 n (k + 1) (by omega) (by omega)
      (fun k' h1 h2 => h k' (by omega) h2)

theorem scanNL_ge_self (b : ByteArray) : ∀ n k, b.size - k = n → k ≤ scanNL b k
  | 0, k, hn => by
    rw [scanNL_unfold, iteF (by simp; omega)]
    exact Nat.le_refl k
  | n + 1, k, hn => by
    rw [scanNL_unfold]
    split
    · exact Nat.le_of_succ_le (scanNL_ge_self b n (k + 1) (by omega))
    · exact Nat.le_refl k

theorem scanNL_ge (b : ByteArray) (e : Nat) :
    ∀ n k, e - k = n → (∀ k', k ≤ k' → k' < e → k' < b.size ∧ b.get! k' ≠ 10) → e ≤ scanNL b k
  | 0, k, hn, _ => Nat.le_trans (by omega) (scanNL_ge_self b _ k rfl)
  | n + 1, k, hn, h => by
    obtain ⟨h1, h2⟩ := h k (Nat.le_refl k) (by omega)
    rw [scanNL_unfold, iteT (by simp [h1, h2])]
    exact scanNL_ge b e n (k + 1) (by omega) (fun k' h3 h4 => h k' (by omega) h4)

def quadX (s : ByteArray) (i : Nat) : Nat :=
  (b64val (s.get! i) <<< 18) ||| (b64val (s.get! (i + 1)) <<< 12) |||
    (b64val (s.get! (i + 2)) <<< 6) ||| b64val (s.get! (i + 3))

def tb (x : Nat) : List UInt8 := [UInt8.ofNat (x >>> 16), UInt8.ofNat (x >>> 8), UInt8.ofNat x]

def decLoop (s : ByteArray) (stop : Nat) (st : ByteArray × Nat) : ByteArray × Nat :=
  forIn (m := Id) Lean.Loop.mk st (fun _ r =>
    if r.2 + 4 ≤ stop then
      pure (ForInStep.yield (((r.1.push (UInt8.ofNat (quadX s r.2 >>> 16))).push
        (UInt8.ofNat (quadX s r.2 >>> 8))).push (UInt8.ofNat (quadX s r.2)), r.2 + 4))
    else pure (ForInStep.done (r.1, r.2)))

theorem b64decode_eq (s : ByteArray) (start stop : Nat) :
    b64decode s start stop =
      (decLoop s stop (ByteArray.emptyWithCapacity ((stop - start) / 4 * 3), start)).1 := rfl

theorem decLoop_eq (s : ByteArray) (stop : Nat) : ∀ n (out : ByteArray) (i : Nat),
    (stop - i) / 4 = n → (decLoop s stop (out, i)).1.data.toList =
      out.data.toList ++ (List.range n).flatMap fun q => tb (quadX s (i + 4 * q))
  | 0, out, i, hn => by
    have h4 : ¬ (i + 4 ≤ stop) := by omega
    unfold decLoop
    rw [forIn_loop_unfold, iteF h4]
    simp only [List.range_zero, List.flatMap_nil, List.append_nil]
    rfl
  | n + 1, out, i, hn => by
    have h4 : i + 4 ≤ stop := by omega
    unfold decLoop
    rw [forIn_loop_unfold, iteT h4]
    change (decLoop s stop _).1.data.toList = _
    rw [decLoop_eq s stop n _ (i + 4) (by omega), List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    have e : ∀ a : Nat, i + 4 * (a + 1) = i + 4 + 4 * a := fun a => by omega
    simp only [ByteArray.data_push, Array.toList_push, List.append_assoc, Nat.mul_zero,
      Nat.add_zero, tb, Nat.succ_eq_add_one, e, List.cons_append,
      List.nil_append]

theorem flatMap3_get (g : Nat → List UInt8) (hg : ∀ q, (g q).length = 3) :
    ∀ Q q r, q < Q → r < 3 → ((List.range Q).flatMap g)[3 * q + r]? = (g q)[r]?
  | 0, _, _, hq, _ => absurd hq (Nat.not_lt_zero _)
  | Q + 1, q, r, hq, hr => by
    have hlen : ((List.range Q).flatMap g).length = 3 * Q := by
      clear hq
      induction Q with
      | zero => rfl
      | succ Q ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hg]; omega
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
    · rw [List.getElem?_append_left (by omega)]
      exact flatMap3_get g hg Q q r hq hr
    · rw [List.getElem?_append_right (by omega), hlen, show 3 * q + r - 3 * q = r by omega]
      simp

theorem b64decode_get (s : ByteArray) (start stop q r : Nat) (hq : q < (stop - start) / 4)
    (hr : r < 3) :
    ((b64decode s start stop).get! (3 * q + r)).toNat =
      (quadX s (start + 4 * q) >>> (16 - 8 * r)) % 256 := by
  rw [bget, b64decode_eq, ← Array.getElem?_toList, decLoop_eq s stop _ _ start rfl]
  have e0 : (ByteArray.emptyWithCapacity ((stop - start) / 4 * 3)).data.toList = [] := rfl
  rw [e0, List.nil_append, flatMap3_get _ (fun _ => rfl) _ q r hq hr]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [tb]

def sbit (bits : ByteArray) (P : Nat) : Bool := ((bits.get! (P / 8)).toNat).testBit (P % 8)

def StInv (bits : ByteArray) (E acc nb pos : Nat) : Prop :=
  acc < 2 ^ nb ∧ (∀ x < nb, acc.testBit x = sbit bits (E + x)) ∧ 8 * pos = E + nb

theorem StInv.pull {bits : ByteArray} {E acc nb pos : Nat} (h : StInv bits E acc nb pos) :
    StInv bits E (acc ||| (bits.get! pos).toNat <<< nb) (nb + 8) (pos + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.or_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))) ?_,
    fun x hx => ?_, by omega⟩
  · rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2 ^ nb)]
    exact Nat.mul_lt_mul_of_pos_right (UInt8.toNat_lt _) (Nat.two_pow_pos _)
  · rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hx' : x < nb
    · rw [h2 x hx']
      have : ¬ x ≥ nb := by omega
      simp [this]
    · have e1 : (E + x) / 8 = pos := by omega
      have e2 : (E + x) % 8 = x - nb := by omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide)
        (by omega)))]
      simp [sbit, e1, e2, show x ≥ nb by omega]

theorem StInv.emit {bits : ByteArray} {E acc nb pos : Nat} (h : StInv bits E acc nb pos)
    (h7 : 7 ≤ nb) : StInv bits (E + 7) (acc >>> 7) (nb - 7) pos ∧
      ∀ t, (acc &&& 127).testBit t = (decide (t < 7) && sbit bits (E + t)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨⟨?_, fun x hx => ?_, by omega⟩, fun t => ?_⟩
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show 7 + (nb - 7) = nb by omega]; exact h1)
  · rw [Nat.testBit_shiftRight, h2 _ (by omega), Nat.add_assoc]
  · rw [Nat.testBit_and, testBit_127]
    by_cases ht : t < 7
    · simp [ht, h2 t (by omega)]
    · simp [ht]

theorem pull_spec {bits : ByteArray} (pl : Nat → Nat → Nat → Nat × Nat × Nat)
    (hpl : ∀ acc nb pos, pl acc nb pos = if nb < 7 then
      pl (acc ||| (bits.get! pos).toNat <<< nb) (nb + 8) (pos + 1) else (acc, nb, pos)) :
    ∀ E acc nb pos, StInv bits E acc nb pos →
      StInv bits E (pl acc nb pos).1 (pl acc nb pos).2.1 (pl acc nb pos).2.2 ∧
        7 ≤ (pl acc nb pos).2.1 := by
  intro E acc nb pos h
  by_cases h7 : nb < 7
  · have h8 : ¬ nb + 8 < 7 := by omega
    rw [hpl, iteT h7, hpl, iteF h8]
    exact ⟨h.pull, Nat.le_of_not_lt h8⟩
  · rw [hpl, iteF h7]
    exact ⟨h, Nat.le_of_not_lt h7⟩

theorem get!_set! (row : ByteArray) (j j' : Nat) (v : UInt8) :
    (row.set! j v).get! j' = if j = j' ∧ j < row.size then v else row.get! j' := by
  rcases row with ⟨data⟩
  simp only [ByteArray.set!, bget, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    ByteArray.size]
  by_cases h1 : j = j'
  · subst h1
    by_cases h2 : j < data.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem size_set! (row : ByteArray) (j : Nat) (v : UInt8) : (row.set! j v).size = row.size := by
  cases row
  simp [ByteArray.set!, ByteArray.size]

theorem get!_replicate (n j : Nat) : (ByteArray.mk (Array.replicate n 0)).get! j = 0 := by
  rw [bget]
  simp only [Array.getElem?_replicate]
  split <;> rfl

def EntryAt (bits : ByteArray) (E v : Nat) : Prop :=
  v < 128 ∧ ∀ t, v.testBit t = (decide (t < 7) && sbit bits (E + t))

def RowInv (bits : ByteArray) (i J : Nat) (dg : UInt8) (row : ByteArray) : Prop :=
  row.size = 4371 ∧ ∀ j < 4371, (j < i → row.get! j = 0) ∧ (j = i → row.get! j = dg) ∧
    (i < j → j < J → ∃ v, row.get! j = UInt8.ofNat v ∧
      EntryAt bits (7 * (entBefore i + (j - i - 1))) v) ∧ (J ≤ j → i < j → row.get! j = 0)

theorem col_step {bits : ByteArray} {i J : Nat} {dg : UInt8} {row : ByteArray}
    {acc nb pos : Nat} (hJ : i < J) (hJ' : J < 4371) (hr : RowInv bits i J dg row)
    (hs : StInv bits (7 * (entBefore i + (J - i - 1))) acc nb pos) (h7 : 7 ≤ nb) :
    RowInv bits i (J + 1) dg (row.set! J (UInt8.ofNat (acc &&& 127))) ∧
      StInv bits (7 * (entBefore i + (J + 1 - i - 1))) (acc >>> 7) (nb - 7) pos := by
  obtain ⟨hs1, hs2⟩ := hs.emit h7
  refine ⟨⟨by rw [size_set!, hr.1], fun j hj => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hr.2 j hj
    simp only [get!_set!, hr.1, hJ', and_true]
    by_cases hjJ : J = j
    · subst hjJ
      simp only [↓reduceIte]
      refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega),
        fun _ _ => ⟨_, rfl, ?_, hs2⟩, fun h => absurd h (by omega)⟩
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    · simp only [hjJ, ↓reduceIte]
      exact ⟨h1, h2, fun h h' => h3 h (by omega), fun h h' => h4 (by omega) h'⟩
  · rw [show 7 * (entBefore i + (J + 1 - i - 1)) = 7 * (entBefore i + (J - i - 1)) + 7 by omega]
    exact hs1

theorem eb_succ : ∀ i < 4371, entBefore (i + 1) = entBefore i + (4370 - i) := by
  intro i hi
  have h2 : (i + 1) * (i + 1 - 1) = i * (i - 1) + 2 * i := by
    cases i with
    | zero => rfl
    | succ k =>
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_comm (k + 1 + 1) (k + 1),
        Nat.mul_succ (k + 1) (k + 1), Nat.mul_succ (k + 1) k]
      omega
  have h3 : (i * (i - 1) + 2 * i) / 2 = i * (i - 1) / 2 + i := Nat.add_mul_div_left _ _ (by decide)
  have h4 : i * (i - 1) ≤ 4370 * i := by
    rw [Nat.mul_comm 4370]
    exact Nat.mul_le_mul_left _ (by omega)
  have h5 : i * (i - 1) / 2 ≤ i * (i - 1) := Nat.div_le_self _ _
  change 4370 * (i + 1) - (i + 1) * (i + 1 - 1) / 2 = 4370 * i - i * (i - 1) / 2 + (4370 - i)
  rw [h2, h3]
  omega

theorem eb_mono {i : Nat} : ∀ {j : Nat}, i ≤ j → j ≤ 4371 → entBefore i ≤ entBefore j
  | 0, h, _ => by
    rw [Nat.le_zero.1 h]
    exact Nat.le_refl _
  | j + 1, h, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h | rfl
    · rw [eb_succ j (by omega)]
      exact Nat.le_trans (eb_mono (Nat.le_of_lt_succ h) (by omega)) (Nat.le_add_right _ _)
    · exact Nat.le_refl _

theorem eb_top : entBefore 4371 = 9550635 := by decide

theorem eb_le {i : Nat} (hi : i ≤ 4371) : entBefore i ≤ 9550635 := eb_top ▸ eb_mono hi (Nat.le_refl _)

noncomputable def kbit (CH : List (Nat × Nat)) (P : Nat) : Bool :=
  (segDec (CH.getD (P / 1536 + 1) (0, 0)).1 64).testBit (P % 1536)

theorem rowOK_spread {Bs : List (List Nat)} {W b0 i : Nat} (h : rowOK Bs W b0 i = true) :
    spread 0 ((W >>> (7 * entBefore i - b0)) &&& ones (7 * (4370 - i))) (4370 - i) =
      recOf Bs i >>> 16 := by
  rw [← spread_eq 13]
  exact Nat.eq_of_beq_eq_true h

theorem shl_mask {K sh m : Nat} (h : sh + m ≤ K) :
    (Nat.shiftLeft (nat_lit 1) K >>> sh) &&& ones m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  change ((1 <<< K) >>> sh &&& ones m).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_ones, Nat.zero_testBit]
  by_cases hb : b < m
  · have : ¬ sh + b ≥ K := by omega
    simp [this]
  · simp [hb]

theorem spread0_zero (n : Nat) : spread 0 0 n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp [testBit_spread0]

theorem okW_get : ∀ (L : List (Nat × Nat)) (c : Nat), okW L c = true → ∀ k < c, k < L.length →
    pieceOK (isNilP (L.drop (k + 1))) (L.getD k (0, 0)) = true
  | [], _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | p :: t, c, h, k, hkc, hk => by
    have hc : 0 < c := by omega
    simp only [okW, hc, ↓reduceIte, Bool.and_eq_true] at h
    cases k with
    | zero => exact h.1
    | succ k =>
      simp only [List.drop_succ_cons, List.getD_cons_succ]
      exact okW_get t (c - 1) h.2 k (by omega) (by simpa using hk)

theorem block_spec {CH : List (Nat × Nat)} {Bs : List (List Nat)} {s : Nat} (hs : s < 69)
    (hlen : CH.length = 43527)
    (hr : rowsOK CH Bs (64 * s) (Nat.min 64 (4371 - 64 * s)) = true)
    (hnz : blockNZ Bs (64 * s) (Nat.min 64 (4371 - 64 * s)) = true) :
    okW (CH.drop (7 * entBefore (64 * s) / 1536 + 1))
        ((7 * entBefore (64 * s + Nat.min 64 (4371 - 64 * s)) + 1535) / 1536 -
          7 * entBefore (64 * s) / 1536) = true ∧
      ∀ k < Nat.min 64 (4371 - 64 * s), ∀ e t,
        (recOf Bs (64 * s + k) / 2 ^ (16 * (e + 1)) % 65536).testBit t =
          (decide (e < 4370 - (64 * s + k)) && decide (t < 7) &&
            kbit CH (7 * entBefore (64 * s + k) + 7 * e + t)) := by
  generalize hc : Nat.min 64 (4371 - 64 * s) = c at hr hnz ⊢
  have hc' : c = min 64 (4371 - 64 * s) := hc.symm
  have hc64 : c ≤ 64 := by omega
  have hic : 64 * s + c ≤ 4371 := by omega
  generalize hp0 : 7 * entBefore (64 * s) / 1536 = p0
  generalize hpe : (7 * entBefore (64 * s + c) + 1535) / 1536 = pe
  have hpe' : pe ≤ 43526 := by
    have := eb_le hic
    omega
  have hp0' : 1536 * p0 ≤ 7 * entBefore (64 * s) := by omega
  have hrows : ∀ k < c, rowOK Bs (winOf (dropP CH (p0 + 1)) (pe - p0)) (1536 * p0) (64 * s + k) =
      true := by
    rw [← hp0, ← hpe]
    exact latRecAnd_true hr
  rw [winOf_eq, winGo_eq _ _ _ 0 0, dropP_eq] at hrows
  have hok : okW (CH.drop (p0 + 1)) (pe - p0) = true := by
    cases hno : okW (CH.drop (p0 + 1)) (pe - p0)
    · have hno' : ¬ okW (CH.drop (p0 + 1)) (pe - p0) = true := by
        rw [hno]
        exact Bool.false_ne_true
      rw [iteF hno'] at hrows
      obtain ⟨k, hk, hk0⟩ := blockNZ_true hnz
      have e := rowOK_spread (hrows k hk)
      have hik : 64 * s + k ≤ 4371 := by omega
      have hb : 7 * entBefore (64 * s + k) - 1536 * p0 + 7 * (4370 - (64 * s + k)) ≤
          1073741824 := by
        have := eb_le hik
        omega
      rw [shl_mask (K := nat_lit 1073741824) hb, spread0_zero] at e
      exact absurd e.symm hk0
    · rfl
  refine ⟨hok, fun k hk e t => ?_⟩
  rw [iteT hok, Nat.zero_or, Nat.shiftLeft_zero] at hrows
  rw [rowOK_field (hrows k hk) e]
  have hi : 64 * s + k < 4371 := by omega
  split
  · rename_i he
    rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases ht : t < 7
    · have hmono := eb_mono (show 64 * s ≤ 64 * s + k by omega) (by omega)
      have hsucc := eb_succ (64 * s + k) hi
      have hmono2 := eb_mono (show 64 * s + k + 1 ≤ 64 * s + c by omega) hic
      generalize hP : 7 * entBefore (64 * s + k) + 7 * e + t = P
      have hb : 7 * entBefore (64 * s + k) - 1536 * p0 + 7 * e + t = P - 1536 * p0 := by omega
      have hP1 : P < 1536 * pe := by omega
      rw [hb, testBit_sumW _ _ _ (by omega) (by simp [hlen]; omega), kbit, getD_drop]
      have e1 : p0 + 1 + (P - 1536 * p0) / 1536 = P / 1536 + 1 := by omega
      have e2 : (P - 1536 * p0) % 1536 = P % 1536 := by omega
      simp [ht, he, e1, e2]
    · simp [ht]
  · rename_i he
    simp [he]

theorem pieces_ok {CH : List (Nat × Nat)} (hlen : CH.length = 43527)
    (hb : ∀ s < 69, okW (CH.drop (7 * entBefore (64 * s) / 1536 + 1))
        ((7 * entBefore (64 * s + Nat.min 64 (4371 - 64 * s)) + 1535) / 1536 -
          7 * entBefore (64 * s) / 1536) = true) :
    ∀ m < 43526, pieceOK (isNilP (CH.drop (m + 2))) (CH.getD (m + 1) (0, 0)) = true := by
  have cover : ∀ s ≤ 68, ∀ m < (7 * entBefore (64 * s + Nat.min 64 (4371 - 64 * s)) + 1535) / 1536,
      ∃ s' ≤ s, 7 * entBefore (64 * s') / 1536 ≤ m ∧
        m < (7 * entBefore (64 * s' + Nat.min 64 (4371 - 64 * s')) + 1535) / 1536 := by
    intro s
    induction s with
    | zero =>
      intro _ m hm
      have e0 : entBefore (64 * 0) = 0 := by decide
      exact ⟨0, Nat.le_refl 0, by rw [e0]; omega, hm⟩
    | succ s ih =>
      intro hs m hm
      by_cases hm' : m < (7 * entBefore (64 * s + Nat.min 64 (4371 - 64 * s)) + 1535) / 1536
      · obtain ⟨s', h1, h2⟩ := ih (by omega) m hm'
        exact ⟨s', by omega, h2⟩
      · refine ⟨s + 1, Nat.le_refl _, ?_, hm⟩
        have hmin : Nat.min 64 (4371 - 64 * s) = 64 := by
          change min 64 (4371 - 64 * s) = 64
          omega
        rw [hmin, show 64 * s + 64 = 64 * (s + 1) by omega] at hm'
        omega
  intro m hm
  have htop : (7 * entBefore (64 * 68 + Nat.min 64 (4371 - 64 * 68)) + 1535) / 1536 = 43526 := by
    decide
  obtain ⟨s, hs, h1, h2⟩ := cover 68 (Nat.le_refl _) m (by rw [htop]; exact hm)
  have := okW_get _ _ (hb s (by omega)) (m - 7 * entBefore (64 * s) / 1536) (by omega)
    (by simp [hlen]; omega)
  rw [List.drop_drop, getD_drop] at this
  rwa [show 7 * entBefore (64 * s) / 1536 + 1 + (m - 7 * entBefore (64 * s) / 1536) = m + 1 by
    omega, show 7 * entBefore (64 * s) / 1536 + 1 + (m - 7 * entBefore (64 * s) / 1536 + 1) =
      m + 2 by omega] at this

theorem mem_codes {c : Nat} : ∀ {L : List (Nat × Nat)}, c ∈ codes L → ∃ p ∈ L, ∃ k < p.2, c = chAt p.1 k
  | [], h => absurd h List.not_mem_nil
  | p :: L, h => by
    rw [codes, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      exact ⟨p, List.mem_cons_self, k, List.mem_range.1 hk, rfl⟩
    · obtain ⟨p', hp', k, hk, rfl⟩ := mem_codes h
      exact ⟨p', List.mem_cons_of_mem _ hp', k, hk, rfl⟩

theorem b64val_eq : ∀ c < 128, b64val (UInt8.ofNat c) = b64v c := by
  decide +kernel

theorem uint8_ne_10 {c : Nat} (hc : c < 128) (h10 : c ≠ 10) : UInt8.ofNat c ≠ 10 := by
  intro h
  have := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hc (by decide))] at this
  exact h10 this

theorem upperBitsOf_eq (t : String) : upperBitsOf t =
    b64decode t.toUTF8 (lineBreakOf t + 1) (scanNL t.toUTF8 (lineBreakOf t + 1)) := rfl

theorem text_spec {CH : List (Nat × Nat)} {Bs : List (List Nat)} (hlen : CH.length = 43527)
    (hd : diagOK (CH.getD 0 (0, 0)) Bs = true)
    (hp : ∀ m < 43526, pieceOK (isNilP (CH.drop (m + 2))) (CH.getD (m + 1) (0, 0)) = true)
    (hl : 9 ≤ (CH.getD 43526 (0, 0)).2) :
    ∀ P < 66854448, sbit (upperBitsOf (String.ofList (CFSG.KC.YModel.charsOf CH))) P = kbit CH P := by
  obtain ⟨q0, ps, rfl⟩ : ∃ q0 ps, CH = q0 :: ps := by
    cases CH with
    | nil => exact absurd hlen (by decide)
    | cons q0 ps => exact ⟨q0, ps, rfl⟩
  have hps : ps.length = 43526 := by simpa using hlen
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons] at hd hp hl
  obtain ⟨h0l, hd⟩ := latAndB_true hd
  obtain ⟨h0n, hd⟩ := latAndB_true hd
  have hq0 : q0.2 = 4372 := Nat.eq_of_beq_eq_true h0l
  generalize hn : nat_lit 4371 = n at hd
  have hdig : ∀ k < 4371, 48 ≤ chAt q0.1 k ∧ chAt q0.1 k ≤ 55 := fun k hk =>
    inR_true (latAndB_true (latRecAnd_true hd k (hn ▸ hk))).1
  have hnl : chAt q0.1 4371 = 10 := Nat.eq_of_beq_eq_true h0n
  have hmid : ∀ m < 43525, (ps.getD m (0, 0)).2 = 256 := by
    intro m hm
    refine (pieceOK_spec (hp m (by omega))).1 ?_
    rw [isNilP_eq]
    simp [hps]
    omega
  have hchar : ∀ m < 43526, ∀ k < (ps.getD m (0, 0)).2,
      isB64 (chAt (ps.getD m (0, 0)).1 k) = true ∨
        (chAt (ps.getD m (0, 0)).1 k = 10 ∧ k + 1 = (ps.getD m (0, 0)).2 ∧ m = 43525) := by
    intro m hm k hk
    rcases (pieceOK_spec (hp m hm)).2.2 k hk with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, ?_⟩
      rw [isNilP_eq] at h3
      simp [hps] at h3
      omega
  have hasc : ∀ c ∈ codes (q0 :: ps), c < 128 := by
    intro c hc
    obtain ⟨p, hp', k, hk, rfl⟩ := mem_codes hc
    rcases List.mem_cons.1 hp' with rfl | hp'
    · rw [hq0] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · have := hdig k hk
        omega
      · rw [hnl]
        decide
    · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hp'
      have e : ps[m] = ps.getD m (0, 0) := by simp [List.getD_eq_getElem?_getD, hm]
      rw [e] at hk ⊢
      rcases hchar m (by omega) k hk with h | ⟨h, -⟩
      · exact (isB64_ok h).1
      · rw [h]
        decide
  generalize ht : String.ofList (CFSG.KC.YModel.charsOf (q0 :: ps)) = t
  have hb : t.toUTF8 = ((codes (q0 :: ps)).map UInt8.ofNat).toByteArray := by
    rw [← ht, toUTF8_eq _ hasc]
  have hget : ∀ k v, (codes (q0 :: ps))[k]? = some v → k < t.toUTF8.size ∧
      t.toUTF8.get! k = UInt8.ofNat v := by
    intro k v hk
    rw [hb, bget]
    have hk' := (List.getElem?_eq_some_iff.1 hk).1
    refine ⟨by simpa using hk', ?_⟩
    simp [List.getElem?_map, hk]
  have hc0 : ∀ k < 4372, (codes (q0 :: ps))[k]? = some (chAt q0.1 k) := by
    intro k hk
    rw [codes, List.getElem?_append_left (by simp [hq0]; omega), List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  have hcm : ∀ m c, m < 43526 → c < (ps.getD m (0, 0)).2 →
      (codes (q0 :: ps))[4372 + (256 * m + c)]? = some (chAt (ps.getD m (0, 0)).1 c) := by
    intro m c hm hc
    rw [codes, List.getElem?_append_right (by simp [hq0])]
    simp only [List.length_map, List.length_range, hq0, Nat.add_sub_cancel_left]
    exact codes_get ps m c (fun m' hm' => hmid m' (by omega)) (by omega) hc
  have hlb : lineBreakOf t = 4371 := by
    rw [lineBreakOf_eq]
    obtain ⟨h1, h2⟩ := hget 4371 _ (hc0 4371 (by decide))
    refine scanNL_exact _ 4371 h1 (by rw [h2, hnl]; rfl) 4371 0 rfl (Nat.zero_le _) ?_
    intro k' _ hk'
    rw [(hget k' _ (hc0 k' (by omega))).2]
    have := hdig k' hk'
    exact uint8_ne_10 (by omega) (by omega)
  have hline : ∀ k', 4372 ≤ k' → k' < 4372 + 11142408 → ∃ v, isB64 v = true ∧
      (codes (q0 :: ps))[k']? = some v := by
    intro k' h1 h2
    have e : k' = 4372 + (256 * ((k' - 4372) / 256) + (k' - 4372) % 256) := by omega
    have hm : (k' - 4372) / 256 < 43526 := by omega
    have hc : (k' - 4372) % 256 < (ps.getD ((k' - 4372) / 256) (0, 0)).2 := by
      by_cases hm' : (k' - 4372) / 256 < 43525
      · rw [hmid _ hm']
        omega
      · have : (k' - 4372) / 256 = 43525 := by omega
        rw [this]
        omega
    have hk := hcm _ _ hm hc
    rw [← e] at hk
    refine ⟨_, ?_, hk⟩
    rcases hchar _ hm _ hc with h | ⟨-, h1, h3⟩
    · exact h
    · rw [h3] at h1
      omega
  have hstop : 4372 + 11142408 ≤ scanNL t.toUTF8 (lineBreakOf t + 1) := by
    rw [hlb]
    refine scanNL_ge _ _ (4372 + 11142408 - 4372) 4372 rfl ?_
    intro k' h1 h2
    obtain ⟨v, hv, hk⟩ := hline k' h1 h2
    obtain ⟨h3, h4⟩ := hget k' v hk
    exact ⟨h3, h4 ▸ uint8_ne_10 (isB64_ok hv).1 (isB64_ok hv).2⟩
  have hquad : ∀ q < 2785602, quadX t.toUTF8 (4372 + 4 * q) =
      quadV (ps.getD (q / 64) (0, 0)).1 (q % 64) := by
    intro q hq
    have hu : ∀ u < 4, b64val (t.toUTF8.get! (4372 + 4 * q + u)) =
        b64v (chAt (ps.getD (q / 64) (0, 0)).1 (4 * (q % 64) + u)) := by
      intro u hu
      have e : 4372 + 4 * q + u = 4372 + (256 * (q / 64) + (4 * (q % 64) + u)) := by omega
      obtain ⟨v, hv, hk⟩ := hline (4372 + 4 * q + u) (by omega) (by omega)
      rw [e] at hk
      have hc : 4 * (q % 64) + u < (ps.getD (q / 64) (0, 0)).2 := by
        by_cases hm' : q / 64 < 43525
        · rw [hmid _ hm']
          omega
        · have : q / 64 = 43525 := by omega
          rw [this]
          omega
      rw [hcm _ _ (by omega) hc] at hk
      obtain rfl := Option.some.inj hk
      have hk' := hcm _ _ (show q / 64 < 43526 by omega) hc
      rw [← e] at hk'
      rw [(hget _ _ hk').2, b64val_eq _ (isB64_ok hv).1]
    have h0 := hu 0 (by decide)
    rw [Nat.add_zero, Nat.add_zero] at h0
    unfold quadX
    change _ = ((b64v (chAt (ps.getD (q / 64) (0, 0)).1 (4 * (q % 64))) <<< 18 |||
        b64v (chAt (ps.getD (q / 64) (0, 0)).1 (4 * (q % 64) + 1)) <<< 12) |||
      (b64v (chAt (ps.getD (q / 64) (0, 0)).1 (4 * (q % 64) + 2)) <<< 6 |||
        b64v (chAt (ps.getD (q / 64) (0, 0)).1 (4 * (q % 64) + 3))))
    rw [h0, hu 1 (by decide), hu 2 (by decide), hu 3 (by decide)]
    exact Nat.or_assoc _ _ _
  intro P hP
  have hQ : P / 24 < (scanNL t.toUTF8 (lineBreakOf t + 1) - (lineBreakOf t + 1)) / 4 := by
    rw [hlb] at hstop ⊢
    omega
  have hB : P / 8 = 3 * (P / 24) + (P / 8) % 3 := by omega
  rw [sbit, upperBitsOf_eq, hB, b64decode_get _ _ _ _ _ hQ (by omega), hlb, hquad _ (by omega)]
  have hs : P % 1536 = 24 * ((P % 1536) / 24) + P % 24 := by omega
  rw [kbit, List.getD_cons_succ, hs, testBit_segDec _ 64 _ _ (by omega) (by omega),
    testBit_tripleOf _ _ (by omega), show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have e1 : (P / 24) / 64 = P / 1536 := by omega
  have e2 : (P / 24) % 64 = (P % 1536) / 24 := by omega
  have e3 : 16 - 8 * ((P / 8) % 3) + P % 8 = 16 - 8 * (P % 24 / 8) + P % 24 % 8 := by omega
  rw [e1, e2, e3]
  simp [show P % 8 < 8 by omega]

def pullL (bits : ByteArray) (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  forIn (m := Id) Lean.Loop.mk st (fun _ s =>
    if s.2.1 < 7 then
      pure (ForInStep.yield (s.1 ||| (bits.get! s.2.2).toNat <<< s.2.1, s.2.1 + 8, s.2.2 + 1))
    else pure (ForInStep.done (s.1, s.2.1, s.2.2)))

theorem pullL_unfold (bits : ByteArray) (acc nb pos : Nat) : pullL bits (acc, nb, pos) =
    if nb < 7 then pullL bits (acc ||| (bits.get! pos).toNat <<< nb, nb + 8, pos + 1)
    else (acc, nb, pos) := by
  unfold pullL
  rw [forIn_loop_unfold]
  by_cases h : nb < 7
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

def colF (bits : ByteArray) (j : Nat) (s : Nat × Nat × Nat × ByteArray) : Nat × Nat × Nat × ByteArray :=
  (fun p : Nat × Nat × Nat => (p.1 >>> 7, p.2.1 - 7, p.2.2, s.2.2.2.set! j (UInt8.ofNat (p.1 &&& 127))))
    (pullL bits (s.1, s.2.1, s.2.2.1))

def rowG (bits : ByteArray) (dgf : Nat → UInt8) (i : Nat) (s : Array ByteArray × Nat × Nat × Nat) :
    Array ByteArray × Nat × Nat × Nat :=
  (fun r : Nat × Nat × Nat × ByteArray => (s.1.push r.2.2.2, r.1, r.2.1, r.2.2.1))
    (forIn (m := Id) [i + 1:4371]
      (s.2.1, s.2.2.1, s.2.2.2, (ByteArray.mk (Array.replicate 4371 0)).set! i (dgf i))
      (fun j s => pure (ForInStep.yield (colF bits j s))))

theorem colF_spec {bits : ByteArray} {i J : Nat} {dg : UInt8} {s : Nat × Nat × Nat × ByteArray}
    (hJ : i < J) (hJ' : J < 4371) (hr : RowInv bits i J dg s.2.2.2)
    (hs : StInv bits (7 * (entBefore i + (J - i - 1))) s.1 s.2.1 s.2.2.1) :
    RowInv bits i (J + 1) dg (colF bits J s).2.2.2 ∧
      StInv bits (7 * (entBefore i + (J + 1 - i - 1))) (colF bits J s).1 (colF bits J s).2.1
        (colF bits J s).2.2.1 := by
  obtain ⟨h1, h2⟩ := pull_spec (fun acc nb pos => pullL bits (acc, nb, pos))
    (fun acc nb pos => pullL_unfold bits acc nb pos) _ s.1 s.2.1 s.2.2.1 hs
  exact col_step hJ hJ' hr h1 h2

theorem inner_spec (bits : ByteArray) (dgf : Nat → UInt8) (i : Nat) (hi : i < 4371)
    (s0 : Nat × Nat × Nat × ByteArray)
    (hr : RowInv bits i (i + 1) (dgf i) s0.2.2.2)
    (hs : StInv bits (7 * entBefore i) s0.1 s0.2.1 s0.2.2.1) :
    ∀ m, i + 1 + m ≤ 4371 →
      RowInv bits i (i + 1 + m) (dgf i) ((List.range' (i + 1) m).foldl (fun s j => colF bits j s) s0).2.2.2 ∧
      StInv bits (7 * (entBefore i + (i + 1 + m - i - 1)))
        ((List.range' (i + 1) m).foldl (fun s j => colF bits j s) s0).1
        ((List.range' (i + 1) m).foldl (fun s j => colF bits j s) s0).2.1
        ((List.range' (i + 1) m).foldl (fun s j => colF bits j s) s0).2.2.1
  | 0, _ => ⟨hr, by simpa using hs⟩
  | m + 1, hm => by
    obtain ⟨h1, h2⟩ := inner_spec bits dgf i hi s0 hr hs m (by omega)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := colF_spec (by omega) (by omega) h1 h2
    rw [show i + 1 + (m + 1) = i + 1 + m + 1 by omega]
    exact this

theorem row0_spec (bits : ByteArray) (i : Nat) (hi : i < 4371) (dg : UInt8) :
    RowInv bits i (i + 1) dg ((ByteArray.mk (Array.replicate 4371 0)).set! i dg) := by
  have hsz : (ByteArray.mk (Array.replicate 4371 0)).size = 4371 := by
    simp [ByteArray.size]
  refine ⟨by rw [size_set!, hsz], fun j hj => ?_⟩
  simp only [get!_set!, hsz, hi, and_true, get!_replicate]
  refine ⟨fun h => ?_, fun h => by simp [h], fun h h' => absurd h' (by omega), fun _ h => ?_⟩
  · rw [iteF (by omega)]
  · rw [iteF (by omega)]

theorem outer_spec (bits : ByteArray) (dgf : Nat → UInt8) : ∀ k, k ≤ 4371 →
    ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s) (Array.mkEmpty 4371, 0, 0, 0)).1.size = k ∧
    (∀ i < k, RowInv bits i 4371 (dgf i)
      ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s) (Array.mkEmpty 4371, 0, 0, 0)).1[i]!) ∧
    StInv bits (7 * entBefore k)
      ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s) (Array.mkEmpty 4371, 0, 0, 0)).2.1
      ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s) (Array.mkEmpty 4371, 0, 0, 0)).2.2.1
      ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s) (Array.mkEmpty 4371, 0, 0, 0)).2.2.2
  | 0, _ => by
    refine ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    have e0 : entBefore 0 = 0 := by decide
    rw [e0]
    exact ⟨Nat.zero_lt_one, fun x hx => absurd hx (Nat.not_lt_zero _), rfl⟩
  | k + 1, hk => by
    obtain ⟨h1, h2, h3⟩ := outer_spec bits dgf k (by omega)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    generalize ((List.range' 0 k).foldl (fun s i => rowG bits dgf i s)
      (Array.mkEmpty 4371, 0, 0, 0)) = s at h1 h2 h3 ⊢
    have hfin := inner_spec bits dgf k (by omega) (s.2.1, s.2.2.1, s.2.2.2,
      (ByteArray.mk (Array.replicate 4371 0)).set! k (dgf k)) (row0_spec bits k (by omega) _) h3
      (4371 - (k + 1)) (by omega)
    rw [show k + 1 + (4371 - (k + 1)) = 4371 by omega] at hfin
    rw [show 7 * (entBefore k + (4371 - k - 1)) = 7 * entBefore (k + 1) by
      rw [eb_succ k (by omega)]; omega] at hfin
    unfold rowG
    have hsz : ([k + 1:4371] : Std.Legacy.Range).size = 4371 - (k + 1) := by
      simp [Std.Legacy.Range.size]
    have hst : ([k + 1:4371] : Std.Legacy.Range).start = k + 1 := rfl
    have hsp : ([k + 1:4371] : Std.Legacy.Range).step = 1 := rfl
    rw [Std.Legacy.Range.forIn_eq_forIn_range', hsz, hst, hsp,
      forIn_list_yield (colF bits) (fun j s => pure (ForInStep.yield (colF bits j s)))
        (fun _ _ => rfl)]
    refine ⟨by simp [h1], fun i hi => ?_, hfin.2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [getElem!_pos _ i (by simp [h1]; omega), Array.getElem_push_lt (by omega),
        ← getElem!_pos _ i (by omega)]
      exact h2 i hi
    · rw [getElem!_pos _ _ (by simp [h1]), Array.getElem_push, dite_eq_right_of_eq_false (by simp [h1])]
      exact hfin.1

theorem rows_spec (t : String) : (basisRowsOf t).size = 4371 ∧ ∀ i < 4371,
    RowInv (upperBitsOf t) i 4371 (UInt8.ofNat (1 <<< (diagExpOf t)[i]!)) (basisRowsOf t)[i]! := by
  generalize hbits : upperBitsOf t = bits
  generalize hdg : (fun i : Nat => UInt8.ofNat (1 <<< (diagExpOf t)[i]!)) = dgf
  have e1 : basisRowsOf t = (forIn (m := Id) [:4371] (Array.mkEmpty 4371, 0, 0, 0)
      (fun i s => pure (ForInStep.yield (rowG bits dgf i s)))).1 := by
    rw [← hbits, ← hdg]
    rfl
  have hdg' : ∀ i : Nat, UInt8.ofNat (1 <<< (diagExpOf t)[i]!) = dgf i := fun i => by rw [← hdg]
  simp only [hdg']
  have hsz : ([:4371] : Std.Legacy.Range).size = 4371 := rfl
  have hst : ([:4371] : Std.Legacy.Range).start = 0 := rfl
  have hsp : ([:4371] : Std.Legacy.Range).step = 1 := rfl
  rw [e1, Std.Legacy.Range.forIn_eq_forIn_range', hsz, hst, hsp,
    forIn_list_yield (rowG bits dgf) (fun i s => pure (ForInStep.yield (rowG bits dgf i s)))
      (fun _ _ => rfl)]
  have houter := outer_spec bits dgf 4371 (Nat.le_refl _)
  exact ⟨houter.1, fun i hi => houter.2.1 i hi⟩

theorem recAnd_nz {Bs : List (List Nat)} (h : nzAll Bs = true) :
    ∀ s < 69, blockNZ Bs (64 * s) (Nat.min 64 (4371 - 64 * s)) = true :=
  latRecAnd_true h

end CFSG.KC.BM.Lat

public section

namespace CFSG.KC.BM.Lat

open CFSG.Monster.B.Dyadic.Native CFSG.KC.BM.B64

theorem diagExpOf_eq {CH : List (Nat × Nat)} {Bs : List (List Nat)}
    (hd : diagOK (getP CH 0) Bs = true) :
    ∀ i < 4371, (diagExpOf (String.ofList (CFSG.KC.YModel.charsOf CH)))[i]! =
      chAt (getP CH 0).1 i - 48 := by
  intro i hi
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, CH = p :: rest := by
    cases CH with
    | nil => exact absurd hd Bool.false_ne_true
    | cons p rest => exact ⟨p, rest, rfl⟩
  have hg : getP (p :: rest) 0 = p := rfl
  rw [hg] at hd ⊢
  obtain ⟨N, len⟩ := p
  obtain ⟨hl, hd⟩ := latAndB_true hd
  obtain ⟨hnl, hd⟩ := latAndB_true hd
  generalize hn : nat_lit 4371 = n at hd
  have hasc : ∀ k ∈ List.range 4372, chAt N k < 128 := by
    intro k hk
    rw [List.mem_range] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨h1, -⟩ := latAndB_true (latRecAnd_true hd k (hn ▸ hk))
      exact Nat.lt_of_le_of_lt (Nat.le_of_ble_eq_true (latAndB_true h1).2) (by decide)
    · rw [Nat.eq_of_beq_eq_true hnl]
      decide
  have hlen : len = 4372 := Nat.eq_of_beq_eq_true hl
  subst hlen
  have hc : CFSG.KC.YModel.charsOf ((N, 4372) :: rest) =
      CFSG.KC.YModel.decChunkC 4372 N (CFSG.KC.YModel.charsOf rest) := rfl
  have hb : (String.ofList (CFSG.KC.YModel.charsOf ((N, 4372) :: rest))).toUTF8 =
      ((List.range 4372).map (fun k => UInt8.ofNat (chAt N k)) ++
        (CFSG.KC.YModel.charsOf rest).flatMap String.utf8EncodeChar).toByteArray := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, hc, decChunkC_eq]
    unfold List.utf8Encode
    rw [List.flatMap_append, flatMap_ascii _ _ hasc]
  have hi' : i < ((List.range 4372).map (fun k => UInt8.ofNat (chAt N k))).length := by
    rw [List.length_map, List.length_range]
    omega
  unfold diagExpOf
  rw [getElem!_pos (Array.ofFn _) i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  simp only
  rw [hb, byteArray_get!, List.data_toByteArray, List.getElem!_toArray,
    getElem!_pos _ i (by rw [List.length_append]; omega), List.getElem_append_left hi',
    List.getElem_map, List.getElem_range,
    UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (chAt_lt N i) (by decide))]

theorem basisRowsOf_eq {CH : List (Nat × Nat)} {Bs : List (List Nat)}
    (hlen : Nat.beq (lenP CH) (nat_lit 43527) = true) (hd : diagOK (getP CH 0) Bs = true)
    (hr : ∀ s < 69, rowsOK CH Bs (64 * s) (Nat.min 64 (4371 - 64 * s)) = true)
    (hnz : nzAll Bs = true) (hl : lastLenOK CH = true) :
    ∀ i j : Nat, i < 4371 → j < 4371 →
      ((basisRowsOf (String.ofList (CFSG.KC.YModel.charsOf CH)))[i]!.get! j).toNat =
        if j < i then 0 else recOf Bs i / 2 ^ (16 * (j - i)) % 65536 := by
  intro i j hi hj
  have hlen' : CH.length = 43527 := by rw [← lenP_eq]; exact Nat.eq_of_beq_eq_true hlen
  have hblk := fun s hs => block_spec (CH := CH) (Bs := Bs) hs hlen' (hr s hs) (recAnd_nz hnz s hs)
  have hpcs := pieces_ok hlen' fun s hs => (hblk s hs).1
  have hl' : 9 ≤ (CH.getD 43526 (0, 0)).2 := by
    rw [← getP_eq]
    exact Nat.le_of_ble_eq_true hl
  have htext := text_spec hlen' (by rw [← getP_eq]; exact hd) hpcs hl'
  obtain ⟨-, hrows⟩ := rows_spec (String.ofList (CFSG.KC.YModel.charsOf CH))
  obtain ⟨-, hrow⟩ := hrows i hi
  obtain ⟨h1, h2, h3, -⟩ := hrow j hj
  by_cases hji : j < i
  · rw [h1 hji, iteT hji]
    rfl
  rw [iteF hji]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hji) with hij | rfl
  · obtain ⟨v, hv, hv1, hv2⟩ := h3 hij hj
    rw [hv, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hv1 (by decide))]
    obtain ⟨-, hf⟩ := hblk (i / 64) (by omega)
    have hk : i % 64 < Nat.min 64 (4371 - 64 * (i / 64)) := by
      change i % 64 < min 64 (4371 - 64 * (i / 64))
      omega
    have hf := hf (i % 64) hk (j - i - 1)
    rw [show 64 * (i / 64) + i % 64 = i by omega, show j - i - 1 + 1 = j - i by omega] at hf
    apply Nat.eq_of_testBit_eq
    intro t
    rw [hv2 t, hf t]
    by_cases ht : t < 7
    · have hsucc := eb_succ i hi
      have hle := eb_le (show i + 1 ≤ 4371 by omega)
      rw [htext _ (by omega), show 7 * (entBefore i + (j - i - 1)) + t =
        7 * entBefore i + 7 * (j - i - 1) + t by omega]
      simp [ht, show j - i - 1 < 4370 - i by omega]
    · simp [ht]
  · rw [h2 rfl, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one, diagExpOf_eq hd i hi]
    rw [getP_eq] at hd
    obtain ⟨-, hd⟩ := latAndB_true hd
    obtain ⟨-, hd⟩ := latAndB_true hd
    generalize hn : nat_lit 4371 = n at hd
    obtain ⟨hdig, hrec⟩ := latAndB_true (latRecAnd_true hd i (hn ▸ hi))
    have hdig : 48 ≤ chAt (CH.getD 0 (0, 0)).1 i ∧ chAt (CH.getD 0 (0, 0)).1 i ≤ 55 :=
      inR_true hdig
    have hrec : recOf Bs i &&& 65535 = 1 <<< (chAt (CH.getD 0 (0, 0)).1 i - 48) :=
      Nat.eq_of_beq_eq_true hrec
    have hmod : recOf Bs i % 65536 = recOf Bs i &&& 65535 :=
      (Nat.and_two_pow_sub_one_eq_mod _ 16).symm
    have hd8 : chAt (CH.getD 0 (0, 0)).1 i - 48 < 8 := by omega
    rw [getP_eq, hmod, hrec, Nat.shiftLeft_eq, Nat.one_mul]
    exact UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le
      (Nat.pow_lt_pow_right (by decide) hd8) (by decide))

end CFSG.KC.BM.Lat

end
