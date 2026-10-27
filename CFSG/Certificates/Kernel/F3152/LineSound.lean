module

public import Certificates.Data.CFSGNative.Fi22Pinned.Forms
public import CFSG.Certificates.Kernel.F3152.LoopSound

public section

namespace CFSG.KS.F3152

open CFSG.F3.Native CFSG.KS.F3L CFSG.Monster.B.Fischer.Native

theorem testBit_orRec (g : Nat → Nat) (q : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| g i) n).testBit q = true ↔
      ∃ i < n, (g i).testBit q = true
  | 0 => by
    change Nat.testBit 0 q = true ↔ _
    simp
  | n + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| g i) n) ||| g n).testBit q =
      true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_orRec g q n]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases e : i = n
      · subst e
        exact Or.inr h
      · exact Or.inl ⟨i, by omega, h⟩

theorem dgK_testBit (q : Nat) : dgK.testBit q = true ↔ ∃ i < 77, q = 78 * i := by
  have e : dgK = Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| (1 <<< (78 * i))) 77 :=
    rfl
  rw [e, testBit_orRec (fun i => 1 <<< (78 * i))]
  simp only [CFSG.F3.Native.testBit_one_shiftLeft, decide_eq_true_eq]

theorem upK_testBit (q : Nat) :
    upK.testBit q = true ↔ ∃ i < 77, 78 * i + 1 ≤ q ∧ q - (78 * i + 1) < 76 - i := by
  have e : upK = Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => acc ||| (mk (76 - i) <<< (78 * i + 1))) 77 := rfl
  rw [e, testBit_orRec (fun i => mk (76 - i) <<< (78 * i + 1))]
  simp only [Nat.testBit_shiftLeft, mk_eq, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_eq, ge_iff_le]

theorem dgK_at {a b : Nat} (ha : a < 77) (hb : b < 77) : dgK.testBit (77 * a + b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    rw [decide_eq_true rfl, dgK_testBit]
    exact ⟨a, ha, by omega⟩
  · rw [decide_eq_false h, Bool.eq_false_iff, ne_eq, dgK_testBit]
    rintro ⟨i, _, hi⟩
    omega

theorem upK_at {a b : Nat} (ha : a < 77) (hb : b < 77) : upK.testBit (77 * a + b) = decide (a < b) := by
  by_cases h : a < b
  · rw [decide_eq_true h, upK_testBit]
    exact ⟨a, ha, by omega, by omega⟩
  · rw [decide_eq_false h, Bool.eq_false_iff, ne_eq, upK_testBit]
    rintro ⟨i, _, h1, h2⟩
    omega

theorem not_upK_dgK (q : Nat) : (upK.testBit q && dgK.testBit q) = false := by
  rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, upK_testBit, dgK_testBit]
  rintro ⟨⟨i, _, h1, h2⟩, ⟨i', _, h3⟩⟩
  omega

theorem trU_testBit (x q : Nat) :
    (trU x).testBit q = true ↔ ∃ a < 77, ∃ b ≤ a, q = 77 * a + b ∧ x.testBit (77 * b + a) = true := by
  have e : trU x = Nat.rec (motive := fun _ => Nat) 0 (fun t acc => acc |||
      (((x >>> t) &&& (dgK &&& mk (78 * (77 - t)))) <<< (77 * t))) 77 := by
    set_option maxRecDepth 100000 in rfl
  rw [e, testBit_orRec (fun t => ((x >>> t) &&& (dgK &&& mk (78 * (77 - t)))) <<< (77 * t))]
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, mk_eq,
    Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  constructor
  · rintro ⟨t, ht, h1, hx, hd, h2⟩
    obtain ⟨i, hi, hq⟩ := (dgK_testBit _).1 hd
    refine ⟨t + i, by omega, i, by omega, by omega, ?_⟩
    have e2 : 77 * i + (t + i) = t + (q - 77 * t) := by omega
    rw [e2]
    exact hx
  · rintro ⟨a, ha, b, hb, hq, hx⟩
    refine ⟨a - b, by omega, by omega, ?_, (dgK_testBit _).2 ⟨b, by omega, by omega⟩, by omega⟩
    have e2 : a - b + (q - 77 * (a - b)) = 77 * b + a := by omega
    rw [e2]
    exact hx

theorem trU_at {x a b : Nat} (ha : a < 77) (hb : b < 77) :
    (trU x).testBit (77 * a + b) = (decide (b ≤ a) && x.testBit (77 * b + a)) := by
  cases h : (trU x).testBit (77 * a + b)
  · symm
    rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    have := (trU_testBit x _).2 ⟨a, ha, b, h1, rfl, h2⟩
    rw [h] at this
    exact Bool.false_ne_true this
  · obtain ⟨a', ha', b', hb', hq, hx⟩ := (trU_testBit x _).1 h
    have e1 : a' = a := by omega
    have e2 : b' = b := by omega
    subst e1 e2
    rw [decide_eq_true hb', hx]
    rfl

theorem offK_succ : ∀ i < 77, offK (i + 1) = offK i + (77 - i) := by decide

theorem offK_mono {i j : Nat} (h : i ≤ j) (hj : j ≤ 77) : offK i ≤ offK j := by
  induction j, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ j _ ih =>
    rw [offK_succ j (by omega)]
    have := ih (by omega)
    omega

theorem offK_77 : offK 77 = 3003 := by decide

theorem offK_uniq {i i' k : Nat} (hi : i < 77) (hi' : i' < 77) (h1 : offK i ≤ k)
    (h2 : k < offK (i + 1)) (h3 : offK i' ≤ k) (h4 : k < offK (i' + 1)) : i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := offK_mono (i := i + 1) (j := i') (by omega) (by omega)
    omega
  · have := offK_mono (i := i' + 1) (j := i) (by omega) (by omega)
    omega

theorem plOf_testBit (x k : Nat) : (plOf x).testBit k = true ↔
    ∃ i < 77, offK i ≤ k ∧ k < offK (i + 1) ∧ x.testBit (78 * i + (k - offK i)) = true := by
  have e : plOf x = Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc |||
      (((x >>> (78 * i)) &&& mk (77 - i)) <<< offK i)) 77 := rfl
  rw [e, testBit_orRec (fun i => ((x >>> (78 * i)) &&& mk (77 - i)) <<< offK i)]
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, mk_eq,
    Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  constructor
  · rintro ⟨i, hi, h1, hx, h2⟩
    refine ⟨i, hi, h1, ?_, hx⟩
    rw [offK_succ i hi]
    omega
  · rintro ⟨i, hi, h1, h2, hx⟩
    refine ⟨i, hi, h1, hx, ?_⟩
    rw [offK_succ i hi] at h2
    omega

theorem pairIdx_eq (i j : Nat) : pairIdx i j = offK i + (j - i) := rfl

theorem plOf_pair (x : Nat) {i j : Nat} (hij : i ≤ j) (hj : j < 77) :
    (plOf x).testBit (pairIdx i j) = x.testBit (77 * i + j) := by
  have hi : i < 77 := by omega
  have hs := offK_succ i hi
  have e : 78 * i + (offK i + (j - i) - offK i) = 77 * i + j := by omega
  rw [pairIdx_eq]
  cases h : (plOf x).testBit (offK i + (j - i))
  · symm
    rw [Bool.eq_false_iff, ne_eq]
    intro hx
    have := (plOf_testBit x (offK i + (j - i))).2 ⟨i, hi, by omega, by omega, by rw [e]; exact hx⟩
    rw [h] at this
    exact Bool.false_ne_true this
  · obtain ⟨i', hi', h1, h2, hx⟩ := (plOf_testBit x _).1 h
    have e' := offK_uniq hi hi' (by omega) (by omega) h1 h2
    subst e'
    rw [e] at hx
    exact hx.symm

theorem plOf_high (x : Nat) {k : Nat} (hk : 3003 ≤ k) : (plOf x).testBit k = false := by
  rw [Bool.eq_false_iff, ne_eq, plOf_testBit]
  rintro ⟨i, hi, _, h2, _⟩
  have := offK_mono (i := i + 1) (j := 77) (by omega) (le_refl _)
  rw [offK_77] at this
  omega

theorem plOf_disj {x y : Nat} (h : ∀ q, (x.testBit q && y.testBit q) = false) (k : Nat) :
    ((plOf x).testBit k && (plOf y).testBit k) = false := by
  rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true]
  rintro ⟨h1, h2⟩
  obtain ⟨i, hi, a1, a2, hx⟩ := (plOf_testBit x k).1 h1
  obtain ⟨i', hi', b1, b2, hy⟩ := (plOf_testBit y k).1 h2
  have e := offK_uniq hi hi' a1 a2 b1 b2
  subst e
  have := h (78 * i + (k - offK i))
  rw [hx, hy] at this
  exact Bool.false_ne_true this.symm

theorem upperOf_p (S : V) (q : Nat) : (upperOf S).p.testBit q =
    (S.p.testBit q && upK.testBit q || S.m.testBit q && dgK.testBit q) := by
  change (S.p &&& upK ||| S.m &&& dgK).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and]

theorem upperOf_m (S : V) (q : Nat) : (upperOf S).m.testBit q =
    (S.m.testBit q && upK.testBit q || S.p.testBit q && dgK.testBit q) := by
  change (S.m &&& upK ||| S.p &&& dgK).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and]

theorem upperOf_disj {S : V} (hS : S.wf = true) (q : Nat) :
    ((upperOf S).p.testBit q && (upperOf S).m.testBit q) = false := by
  rw [upperOf_p, upperOf_m]
  have h1 := V.not_both hS q
  have h2 := not_upK_dgK q
  revert h1 h2
  cases S.p.testBit q <;> cases S.m.testBit q <;> cases upK.testBit q <;> cases dgK.testBit q <;>
    decide

theorem upperOf_low {S : V} {a b : Nat} (ha : a < 77) (hb : b < 77) (hab : b < a) :
    (upperOf S).p.testBit (77 * a + b) = false ∧ (upperOf S).m.testBit (77 * a + b) = false := by
  rw [upperOf_p, upperOf_m, upK_at ha hb, dgK_at ha hb, decide_eq_false (by omega),
    decide_eq_false (by omega)]
  simp

theorem val_add_at {a b : V} {j : Nat} (ha : (a.p.testBit j && a.m.testBit j) = false)
    (hb : (b.p.testBit j && b.m.testBit j) = false) : (a.add b).val j = a.val j + b.val j := by
  rw [V.val_eq_bitVal, V.val_eq_bitVal, V.val_eq_bitVal, (V.add_bits a b j).1, (V.add_bits a b j).2]
  revert ha hb
  cases a.p.testBit j <;> cases a.m.testBit j <;> cases b.p.testBit j <;> cases b.m.testBit j <;>
    decide

theorem val_blk {L : V} {i j : Nat} (hj : j < 77) : (blk 77 L i).val j = L.val (77 * i + j) := by
  rw [V.val_eq_bitVal, V.val_eq_bitVal, blk_p, blk_m]
  simp [hj]

theorem bitVal_toNat {p m : Bool} (h : (p && m) = false) :
    ((p.toNat + 2 * m.toNat : Nat) : ZMod 3) = bitVal p m := by
  revert h
  cases p <;> cases m <;> decide

theorem bytesK_spec : ∀ (n N P M : Nat), bytesK n N P M = true →
    (∀ m < n, (N >>> (8 * m)) % 256 = 40 + tri4 ((P >>> (4 * m)) % 16) +
      2 * tri4 ((M >>> (4 * m)) % 16)) ∧ N >>> (8 * n) = 10
  | 0, N, P, M, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Nat.beq M 0) (Nat.beq P 0)) (Nat.beq N 10) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    exact ⟨fun m hm => absurd hm (Nat.not_lt_zero m), Nat.eq_of_beq_eq_true h.1⟩
  | n + 1, N, P, M, h => by
    change Bool.rec (motive := fun _ => Bool) false (bytesK n (N >>> 8) (P >>> 4) (M >>> 4))
      (Nat.beq (N &&& 255) (40 + (tri4 (P &&& 15) + 2 * tri4 (M &&& 15)))) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := bytesK_spec n _ _ _ h2
    have e255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
    have e15 : ∀ x : Nat, x &&& 15 = x % 16 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
    have h1' := Nat.eq_of_beq_eq_true h1
    rw [e255, e15, e15] at h1'
    refine ⟨fun m hm => ?_, ?_⟩
    · rcases m with _ | m
      · simp only [Nat.mul_zero, Nat.shiftRight_zero]
        omega
      · have := ih1 m (by omega)
        rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, ← Nat.shiftRight_add] at this
        have e8 : 8 * (m + 1) = 8 + 8 * m := by omega
        have e4 : 4 * (m + 1) = 4 + 4 * m := by omega
        rw [e8, e4]
        exact this
    · rw [← Nat.shiftRight_add] at ih2
      have e8 : 8 * (n + 1) = 8 + 8 * n := by omega
      rw [e8]
      exact ih2

theorem bytesK_inj : ∀ (n N N' P M : Nat), bytesK n N P M = true → bytesK n N' P M = true → N = N'
  | 0, N, N', P, M, h, h' => by
    have a := (bytesK_spec 0 N P M h).2
    have b := (bytesK_spec 0 N' P M h').2
    simp only [Nat.mul_zero, Nat.shiftRight_zero] at a b
    rw [a, b]
  | n + 1, N, N', P, M, h, h' => by
    change Bool.rec (motive := fun _ => Bool) false (bytesK n (N >>> 8) (P >>> 4) (M >>> 4))
      (Nat.beq (N &&& 255) (40 + (tri4 (P &&& 15) + 2 * tri4 (M &&& 15)))) = true at h
    change Bool.rec (motive := fun _ => Bool) false (bytesK n (N' >>> 8) (P >>> 4) (M >>> 4))
      (Nat.beq (N' &&& 255) (40 + (tri4 (P &&& 15) + 2 * tri4 (M &&& 15)))) = true at h'
    rw [bAnd_eq, Bool.and_eq_true] at h h'
    have e1 := bytesK_inj n _ _ _ _ h.2 h'.2
    have e2 : N &&& 255 = N' &&& 255 := by
      rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h'.1]
    rw [Nat.and_two_pow_sub_one_eq_mod N 8, Nat.and_two_pow_sub_one_eq_mod N' 8] at e2
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at e1
    have := Nat.div_add_mod N (2 ^ 8)
    have := Nat.div_add_mod N' (2 ^ 8)
    omega

theorem tri4_eq (x : Nat) : tri4 (x % 16) = (x.testBit 0).toNat + 3 * (x.testBit 1).toNat +
    9 * (x.testBit 2).toNat + 27 * (x.testBit 3).toNat := by
  have e16 : (16 : Nat) = 2 ^ 4 := rfl
  have e : ∀ u < 4, ((x % 16) >>> u) &&& 1 = (x.testBit u).toNat := by
    intro u hu
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, ← Nat.toNat_testBit, e16,
      Nat.testBit_mod_two_pow, decide_eq_true hu, Bool.true_and]
  change ((x % 16) &&& 1) + (3 * (((x % 16) >>> 1) &&& 1) + (9 * (((x % 16) >>> 2) &&& 1) +
    27 * (((x % 16) >>> 3) &&& 1))) = _
  have e0 := e 0 (by norm_num)
  rw [Nat.shiftRight_zero] at e0
  rw [e0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  omega

theorem digit : ∀ p0 p1 p2 p3 m0 m1 m2 m3 : Bool, (p0 && m0) = false → (p1 && m1) = false →
    (p2 && m2) = false → (p3 && m3) = false → ∀ u < 4,
    (40 + (p0.toNat + 3 * p1.toNat + 9 * p2.toNat + 27 * p3.toNat) +
      2 * (m0.toNat + 3 * m1.toNat + 9 * m2.toNat + 27 * m3.toNat) - 40) / 3 ^ u % 3 =
      [p0.toNat + 2 * m0.toNat, p1.toNat + 2 * m1.toNat, p2.toNat + 2 * m2.toNat,
        p3.toNat + 2 * m3.toNat].getD u 0 := by
  decide

theorem toNat_disj {p m : Bool} (h : (p && m) = false) : p.toNat + m.toNat ≤ 1 := by
  revert h
  cases p <;> cases m <;> decide

theorem lineOK_parts {S : V} {N : Nat} (h : lineOK S N = true) :
    S.wf = true ∧ S = symOf (upperOf S) ∧
      bytesK 751 N (plOf (upperOf S).p) (plOf (upperOf S).m) = true := by
  unfold lineOK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, eqV_iff.1 h2, h3⟩
  unfold V.wf
  rw [beq_iff_eq]
  exact Nat.eq_of_beq_eq_true h1

theorem lineOK_wf {S : V} {N : Nat} (h : lineOK S N = true) : S.wf = true := (lineOK_parts h).1

theorem lineOK_inj {S : V} {N N' : Nat} (h : lineOK S N = true) (h' : lineOK S N' = true) :
    N = N' :=
  bytesK_inj 751 N N' _ _ (lineOK_parts h).2.2 (lineOK_parts h').2.2

theorem high_false {S : V} {q : Nat} (hq : 5929 ≤ q) :
    (upperOf S).p.testBit q = false ∧ (upperOf S).m.testBit q = false ∧
      (trU (upperOf S).p).testBit q = false ∧ (trU (upperOf S).m).testBit q = false := by
  have hu : upK.testBit q = false := by
    rw [Bool.eq_false_iff, ne_eq, upK_testBit]
    rintro ⟨i, _, h1, h2⟩
    omega
  have hd : dgK.testBit q = false := by
    rw [Bool.eq_false_iff, ne_eq, dgK_testBit]
    rintro ⟨i, _, h1⟩
    omega
  have ht : ∀ x, (trU x).testBit q = false := by
    intro x
    rw [Bool.eq_false_iff, ne_eq, trU_testBit]
    rintro ⟨a, _, b, _, h1, _⟩
    omega
  rw [upperOf_p, upperOf_m, hu, hd, ht, ht]
  simp

set_option exponentiation.threshold 6000 in
theorem lineOK_lt {S : V} {N : Nat} (h : lineOK S N = true) : S.p < 2 ^ 5929 ∧ S.m < 2 ^ 5929 := by
  obtain ⟨-, hsym, -⟩ := lineOK_parts h
  have hb : ∀ q, 5929 ≤ q → S.p.testBit q = false ∧ S.m.testBit q = false := by
    intro q hq
    obtain ⟨a1, a2, a3, a4⟩ := high_false (S := S) hq
    rw [hsym]
    unfold symOf
    rw [(V.add_bits _ _ q).1, (V.add_bits _ _ q).2]
    dsimp only
    simp [a1, a2, a3, a4]
  exact ⟨Nat.lt_pow_two_of_testBit _ fun q hq => (hb q hq).1,
    Nat.lt_pow_two_of_testBit _ fun q hq => (hb q hq).2⟩

theorem lineOK_code {S : V} {N : Nat} (h : lineOK S N = true) {m : Nat} (hm : m < 752) :
    (N >>> (8 * m)) % 256 < 128 := by
  obtain ⟨hS, -, hB⟩ := lineOK_parts h
  obtain ⟨h1, h2⟩ := bytesK_spec 751 N _ _ hB
  have hdisj := plOf_disj (upperOf_disj hS)
  by_cases hm' : m < 751
  · rw [h1 m hm', tri4_eq, tri4_eq]
    simp only [Nat.testBit_shiftRight]
    have := toNat_disj (hdisj (4 * m + 0))
    have := toNat_disj (hdisj (4 * m + 1))
    have := toNat_disj (hdisj (4 * m + 2))
    have := toNat_disj (hdisj (4 * m + 3))
    omega
  · have e : m = 751 := by omega
    rw [e, h2]
    norm_num

theorem trit_planes {S : V} {N : Nat} (h : lineOK S N = true) {b : ByteArray} {off : Nat}
    (hb : ∀ m < 752, (b.get! (off + m)).toNat = (N >>> (8 * m)) % 256) {k : Nat} (hk : k < 3004) :
    trit b off k = ((plOf (upperOf S).p).testBit k).toNat +
      2 * ((plOf (upperOf S).m).testBit k).toNat := by
  obtain ⟨hS, -, hB⟩ := lineOK_parts h
  obtain ⟨h1, -⟩ := bytesK_spec 751 N _ _ hB
  have hdisj := plOf_disj (upperOf_disj hS)
  obtain ⟨w, u, hu, rfl⟩ : ∃ w u, u < 4 ∧ k = 4 * w + u :=
    ⟨k / 4, k % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 4).symm⟩
  have hw : (4 * w + u) / 4 = w := by omega
  have hu' : (4 * w + u) % 4 = u := by omega
  unfold trit
  rw [hw, hu', hb w (by omega), h1 w (by omega), tri4_eq, tri4_eq]
  simp only [Nat.testBit_shiftRight]
  rw [digit _ _ _ _ _ _ _ _ (hdisj _) (hdisj _) (hdisj _) (hdisj _) u hu]
  interval_cases u <;> rfl

theorem trit_line {S : V} {N : Nat} (h : lineOK S N = true) {b : ByteArray} {off : Nat}
    (hb : ∀ m < 752, (b.get! (off + m)).toNat = (N >>> (8 * m)) % 256) {i j : Nat} (hij : i ≤ j)
    (hj : j < 77) :
    (trit b off (pairIdx i j) : ZMod 3) = (upperOf S).val (77 * i + j) := by
  have hk3 : pairIdx i j < 3003 := by
    rw [pairIdx_eq]
    have := offK_mono (i := i + 1) (j := 77) (by omega) (le_refl _)
    rw [offK_77, offK_succ i (by omega)] at this
    omega
  rw [trit_planes h hb (by omega), bitVal_toNat (plOf_disj (upperOf_disj (lineOK_parts h).1) _),
    plOf_pair _ hij hj, plOf_pair _ hij hj, V.val_eq_bitVal]

theorem formRows_val (b : ByteArray) (off : Nat) {i j : Nat} (hi : i < 77) (hj : j < 77) :
    (formRows b off)[i]!.val j = if i ≤ j then (trit b off (pairIdx i j) : ZMod 3) else 0 := by
  unfold formRows
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn, V.val_ofFn,
    ite_eq_left hj]
  split_ifs <;> simp

theorem formRows_size (b : ByteArray) (off : Nat) : (formRows b off).size = 77 := by
  unfold formRows
  rw [Array.size_ofFn]

theorem formRows_wf (b : ByteArray) (off : Nat) : RowsWF (formRows b off) := by
  intro i
  by_cases hi : i < 77
  · unfold formRows
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
    exact V.wf_ofFn _ _
  · rw [getElem!_neg _ i (by rw [formRows_size]; exact hi)]
    exact V.wf_zero

theorem polarRows_get (b : ByteArray) (off : Nat) {i : Nat} (hi : i < 77) :
    (polarRows b off)[i]! = (formRows b off)[i]!.add (transpose 77 (formRows b off))[i]! := by
  unfold polarRows
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem polarRows_val (b : ByteArray) (off : Nat) {i j : Nat} (hi : i < 77) (hj : j < 77) :
    (polarRows b off)[i]!.val j =
      (formRows b off)[i]!.val j + (formRows b off)[j]!.val i := by
  rw [polarRows_get b off hi, V.val_add (formRows_wf b off i) (RowsWF.transpose 77 _ i)]
  have := congrFun (congrFun (toMat_transpose (d := 77) (formRows b off)) ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, Matrix.transpose_apply, toMat_apply] at this
  rw [this]

theorem testBit_add_lt {a c : V} {j : Nat} (ha : a.p.testBit j = false ∧ a.m.testBit j = false)
    (hc : c.p.testBit j = false ∧ c.m.testBit j = false) :
    (a.add c).p.testBit j = false ∧ (a.add c).m.testBit j = false := by
  rw [(V.add_bits a c j).1, (V.add_bits a c j).2, ha.1, ha.2, hc.1, hc.2]
  exact ⟨rfl, rfl⟩

theorem ofFn_high (f : Nat → Nat) {j : Nat} (hj : 77 ≤ j) :
    (V.ofFn 77 f).p.testBit j = false ∧ (V.ofFn 77 f).m.testBit j = false := by
  rw [ofFn_eq_fold]
  obtain ⟨h1, h2⟩ := fold_ofFnStep_bits f j 77
  have hj' : ¬ j < 77 := by omega
  rw [h1, h2]
  simp [hj']

theorem canon_of_high {a : V} (hw : a.wf = true)
    (h : ∀ j, 77 ≤ j → a.p.testBit j = false ∧ a.m.testBit j = false) :
    (a.wf && a.p >>> 77 == 0 && a.m >>> 77 == 0) = true := by
  have hp : a.p < 2 ^ 77 := Nat.lt_pow_two_of_testBit _ fun j hj => (h j hj).1
  have hm : a.m < 2 ^ 77 := Nat.lt_pow_two_of_testBit _ fun j hj => (h j hj).2
  rw [hw, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp,
    Nat.div_eq_of_lt hm]
  rfl

theorem polarRows_size (b : ByteArray) (off : Nat) : (polarRows b off).size = 77 := by
  unfold polarRows
  rw [Array.size_ofFn]

theorem formRows_get (b : ByteArray) (off : Nat) {i : Nat} (hi : i < 77) :
    (formRows b off)[i]! = V.ofFn 77 fun j => if i ≤ j then trit b off (pairIdx i j) else 0 := by
  unfold formRows
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem transpose_get (X : Array V) {i : Nat} (hi : i < 77) :
    (transpose 77 X)[i]! = V.ofFn 77 fun i' => X[i']!.get i := by
  unfold transpose
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem canonRow_polarRows (b : ByteArray) (off : Nat) {i : Nat} (hi : i < 77) :
    ((polarRows b off)[i]!.wf && (polarRows b off)[i]!.p >>> 77 == 0 &&
      (polarRows b off)[i]!.m >>> 77 == 0) = true := by
  rw [polarRows_get b off hi]
  refine canon_of_high (V.wf_add (formRows_wf b off i) (RowsWF.transpose 77 _ i)) fun j hj => ?_
  apply testBit_add_lt
  · rw [formRows_get b off hi]
    exact ofFn_high _ hj
  · rw [transpose_get _ hi]
    exact ofFn_high _ hj

theorem polar_of_line {S : V} {N : Nat} (h : lineOK S N = true) {b : ByteArray} {off : Nat}
    (hb : ∀ m < 752, (b.get! (off + m)).toNat = (N >>> (8 * m)) % 256) :
    polarRows b off = unlane 77 S := by
  obtain ⟨hS, hsym, -⟩ := lineOK_parts h
  set U := upperOf S with hU
  have hUd := upperOf_disj hS
  have hT : ∀ q, ((trU U.p).testBit q && (trU U.m).testBit q) = false := by
    intro q
    rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true]
    rintro ⟨h1, h2⟩
    obtain ⟨a, ha, c, hc, hq, hx⟩ := (trU_testBit _ _).1 h1
    obtain ⟨a', ha', c', hc', hq', hy⟩ := (trU_testBit _ _).1 h2
    have e1 : a' = a := by omega
    have e2 : c' = c := by omega
    rw [e1, e2] at hy
    have := hUd (77 * c + a)
    rw [hx, hy] at this
    exact Bool.false_ne_true this.symm
  have hSv : ∀ a c, a < 77 → c < 77 → S.val (77 * a + c) =
      U.val (77 * a + c) + (if c ≤ a then U.val (77 * c + a) else 0) := by
    intro a c ha hc
    have e : S.val (77 * a + c) = (symOf U).val (77 * a + c) := by rw [← hsym]
    rw [e]
    unfold symOf
    rw [val_add_at (hUd _) (hT _)]
    congr 1
    rw [V.val_eq_bitVal]
    change bitVal ((trU U.p).testBit (77 * a + c)) ((trU U.m).testBit (77 * a + c)) = _
    rw [trU_at ha hc, trU_at ha hc]
    by_cases hca : c ≤ a
    · rw [ite_eq_left hca, decide_eq_true hca, Bool.true_and, Bool.true_and, V.val_eq_bitVal]
    · rw [ite_eq_right hca, decide_eq_false hca, Bool.false_and, Bool.false_and]
      rfl
  have hlow : ∀ a c, a < 77 → c < 77 → c < a → U.val (77 * a + c) = 0 := by
    intro a c ha hc hca
    obtain ⟨h1, h2⟩ := upperOf_low (S := S) ha hc hca
    rw [V.val_eq_bitVal, h1, h2]
    rfl
  have key : ∀ i < 77, (polarRows b off)[i]! = (unlane 77 S)[i]! := by
    intro i hi
    apply V.eq_of_canon (d := 77) (canonRow_polarRows b off hi)
      ((canonM_spec (canonM_unlane 77 hS)).2 i (by rw [unlane_size]; exact hi))
    intro j hj
    rw [polarRows_val b off hi hj, unlane_get S hi, val_blk hj,
      formRows_val b off hi hj, formRows_val b off hj hi, hSv i j hi hj]
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · rw [ite_eq_left hij.le, ite_eq_right (by omega), ite_eq_right (by omega),
        trit_line h hb hij.le hj]
    · rw [ite_eq_left le_rfl, ite_eq_left le_rfl, trit_line h hb le_rfl hj]
    · rw [ite_eq_right (by omega), ite_eq_left hij.le, ite_eq_left hij.le, trit_line h hb hij.le hi,
        hlow i j hi hj hij]
  have hPs := polarRows_size b off
  have hQs := unlane_size 77 S
  generalize polarRows b off = P at key hPs
  generalize unlane 77 S = Q at key hQs
  apply Array.ext (hPs.trans hQs.symm)
  intro i h1 h2
  have := key i (by omega)
  rwa [getElem!_pos P i h1, getElem!_pos Q i h2] at this

end CFSG.KS.F3152

end
