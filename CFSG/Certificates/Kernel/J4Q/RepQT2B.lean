module

public import Certificates.Data.Kernel.J4Q.QT2A
public import CFSG.Certificates.Kernel.J4Q.RepQT2A
public import CFSG.Sporadic.J4.QTOutMatNative

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

private theorem v2N_eq_toNat (a : V2) : v2N a = a.toNat := by
  unfold v2N V2.toNat
  rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
    Nat.shiftLeft_eq]
  omega

private theorem lt64B (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

private theorem v2N_testBitB (v : V2) (k : Nat) :
    (v2N v).testBit k = if k < 64 then v.lo.toNat.testBit k else v.hi.toNat.testBit (k - 64) := by
  change (v.lo.toNat ||| (v.hi.toNat <<< 64)).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < 64
  · have h1 : ¬ k ≥ 64 := by omega
    simp [hk, h1]
  · have h1 : k ≥ 64 := by omega
    have h2 : v.lo.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64B v.lo) (Nat.pow_le_pow_right (by omega) h1))
    simp [hk, h1, h2]

private theorem wf_iffB (v : V2) : v.wf = true ↔ v.hi.toNat < 2 ^ 48 := by
  unfold V2.wf
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, UInt64.toNat_zero]
  have : (48 : UInt64).toNat % 64 = 48 := rfl
  rw [this, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 48))
    · exact h
  · exact Or.inr

private theorem v2N_ltB (v : V2) : v2N v < 2 ^ 128 := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  rw [v2N_testBitB, ite_eq_right (by omega)]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (lt64B v.hi) (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem wf_bitB {v : V2} (hv : v.wf = true) {k : Nat} (hk : 112 ≤ k) :
    (v2N v).testBit k = false := by
  rw [wf_iffB] at hv
  rw [v2N_testBitB, ite_eq_right (by omega)]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem v2N_injB {a b : V2} (h : v2N a = v2N b) : a = b := by
  have hlo : a.lo.toNat = b.lo.toNat := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 64
    · have e := congrArg (fun x => x.testBit j) h
      rw [v2N_testBitB, v2N_testBitB, ite_eq_left hj, ite_eq_left hj] at e
      exact e
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64B _) (Nat.pow_le_pow_right (by omega)
        (by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64B _)
        (Nat.pow_le_pow_right (by omega) (by omega)))]
  have hhi : a.hi.toNat = b.hi.toNat := by
    apply Nat.eq_of_testBit_eq
    intro j
    have e := congrArg (fun x => x.testBit (j + 64)) h
    rw [v2N_testBitB, v2N_testBitB, ite_eq_right (by omega), ite_eq_right (by omega),
      Nat.add_sub_cancel] at e
    exact e
  obtain ⟨al, ah⟩ := a
  obtain ⟨bl, bh⟩ := b
  rw [V2.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp hlo, UInt64.toNat_inj.mp hhi⟩

private theorem foldr_bitsB (g : Nat → Nat) (L : List Nat) (k : Nat) :
    (L.foldr (fun i acc => Nat.lor (g i) acc) 0).testBit k = L.any (fun i => (g i).testBit k) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.any_cons, ← ih]
    exact Nat.testBit_or _ _ _

private theorem encR_bitB (X : Array V2) (p : Nat) :
    (encR X).testBit p =
      (decide (p / 128 < 112) && (v2N (X[p / 128]?.getD V2.zero)).testBit (p % 128)) := by
  unfold encR
  rw [foldr_bitsB]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Array.getD_eq_getD_getElem?]
  constructor
  · rintro ⟨i, hi, h2⟩
    change ((v2N (X[i]?.getD V2.zero)) <<< (128 * i)).testBit p = true at h2
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨h1, h2⟩ := h2
    have hlt : p - 128 * i < 128 := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_ltB _)
        (Nat.pow_le_pow_right (by omega) (by omega)))] at h2
      exact Bool.false_ne_true h2
    have e1 : p / 128 = i := by omega
    have e2 : p % 128 = p - 128 * i := by omega
    rw [e1, e2]
    exact ⟨hi, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p / 128, h1, ?_⟩
    change ((v2N (X[p / 128]?.getD V2.zero)) <<< (128 * (p / 128))).testBit p = true
    rw [Nat.testBit_shiftLeft]
    have e2 : p - 128 * (p / 128) = p % 128 := by omega
    rw [e2, h2]
    simp only [Bool.and_true, decide_eq_true_eq]
    omega

private theorem v2N_xorB (a b : V2) : v2N (a.xor b) = v2N a ^^^ v2N b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, v2N_testBitB, v2N_testBitB, v2N_testBitB]
  change (if j < 64 then (a.lo ^^^ b.lo).toNat.testBit j else (a.hi ^^^ b.hi).toNat.testBit (j - 64)) = _
  rw [UInt64.toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor]
  by_cases h : j < 64 <;> simp [h]

private theorem shl_one_toNatB (j : Nat) :
    ((1 : UInt64) <<< UInt64.ofNat (j % 64)).toNat = 2 ^ (j % 64) := by
  have hj : j % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  have e1 : j % 64 % 2 ^ 64 % 64 = j % 64 := by
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj (by decide)), Nat.mod_eq_of_lt hj]
  rw [e1, UInt64.toNat_one, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hj)

private theorem setBit_bitsB (v : V2) {j : Nat} (hj : j < 112) (k : Nat) :
    (v2N (v.setBit j)).testBit k = ((v2N v).testBit k || decide (k = j)) := by
  unfold V2.setBit
  by_cases h : j / 64 = 0
  · simp only [h, ↓reduceIte]
    rw [v2N_testBitB, v2N_testBitB]
    have hm : j % 64 = j := Nat.mod_eq_of_lt (by omega)
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNatB, hm, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        simp
      · have e' : ¬ j = k := fun h => e h.symm
        simp [e, e']
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
  · simp only [h, ↓reduceIte]
    rw [v2N_testBitB, v2N_testBitB]
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNatB, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        have : k % 64 = k - 64 := by omega
        simp [this]
      · have e' : ¬ j % 64 = k - 64 := by omega
        simp [e, e']

private theorem ofFn_bitsB (f : Nat → Bool) (k : Nat) :
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
        rw [setBit_bitsB _ (by omega), ih (by omega)]
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

private noncomputable def xsumB (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ f k) n

private theorem xsumB_succ (f : Nat → Nat) (n : Nat) : xsumB f (n + 1) = xsumB f n ^^^ f n := rfl

private theorem xsumB_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) →
    xsumB f n = xsumB g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [xsumB_succ, xsumB_succ, xsumB_congr (fun k hk => h k (by omega)), h n (by omega)]

private theorem xsumB_add (f : Nat → Nat) (a : Nat) : ∀ b,
    xsumB f (a + b) = xsumB f a ^^^ xsumB (fun i => f (a + i)) b
  | 0 => by rw [Nat.add_zero]; exact (Nat.xor_zero _).symm
  | b + 1 => by
    rw [← Nat.add_assoc, xsumB_succ, xsumB_add f a b, xsumB_succ, Nat.xor_assoc]

private theorem xsumB_blocks (f : Nat → Nat) : ∀ n,
    xsumB f (8 * n) = xsumB (fun q => xsumB (fun i => f (8 * q + i)) 8) n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ, xsumB_add, xsumB_blocks f n]
    rfl

private noncomputable def bx (g : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => acc ^^ g k) n

private theorem bx_succ (g : Nat → Bool) (n : Nat) : bx g (n + 1) = (bx g n ^^ g n) := rfl

private theorem xsumB_bit (f : Nat → Nat) (j : Nat) : ∀ n,
    (xsumB f n).testBit j = bx (fun k => (f k).testBit j) n
  | 0 => Nat.zero_testBit j
  | n + 1 => by rw [xsumB_succ, bx_succ, Nat.testBit_xor, xsumB_bit f j n]

private theorem bx_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ k < n, f k = g k) → bx f n = bx g n
  | 0, _ => rfl
  | n + 1, h => by rw [bx_succ, bx_succ, bx_congr (fun k hk => h k (by omega)), h n (by omega)]

private theorem bx_and_left (a : Bool) (g : Nat → Bool) : ∀ n,
    (a && bx g n) = bx (fun k => a && g k) n
  | 0 => by simp [bx]
  | n + 1 => by
    rw [bx_succ, bx_succ, ← bx_and_left a g n]
    cases a <;> simp

private theorem bx_and_right (b : Bool) (g : Nat → Bool) : ∀ n,
    (bx g n && b) = bx (fun k => g k && b) n
  | 0 => by simp [bx]
  | n + 1 => by
    rw [bx_succ, bx_succ, ← bx_and_right b g n]
    cases b <;> simp

private theorem bx_xor (f g : Nat → Bool) : ∀ n, bx (fun k => f k ^^ g k) n = (bx f n ^^ bx g n)
  | 0 => rfl
  | n + 1 => by
    rw [bx_succ, bx_succ, bx_succ, bx_xor f g n]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

private theorem bx_swap (g : Nat → Nat → Bool) (m : Nat) : ∀ n,
    bx (fun k => bx (fun l => g k l) m) n = bx (fun l => bx (fun k => g k l) n) m
  | 0 => by
    have : ∀ m, bx (fun _ => false) m = false := fun m => by
      induction m with
      | zero => rfl
      | succ m ih => rw [bx_succ, ih]; rfl
    exact (this m).symm
  | n + 1 => by
    rw [bx_succ, bx_swap g m n, ← bx_xor]
    rfl

private theorem bx_single (a : Nat → Bool) (j : Nat) : ∀ n,
    bx (fun k => a k && decide (k = j)) n = (decide (j < n) && a j)
  | 0 => by simp [bx]
  | n + 1 => by
    rw [bx_succ, bx_single a j n]
    by_cases e : n = j
    · subst e
      simp
    · have h1 : j < n + 1 ↔ j < n := by omega
      simp [e, h1]

private theorem frEntry_v2NB (Y : Array V2) (k c : Nat) : v2N (frEntry Y k c) =
    xsumB (fun i => if c.testBit i then v2N (Y[8 * k + i]?.getD V2.zero) else 0) 8 := by
  have key : ∀ n, v2N ((List.range n).foldl (fun acc i =>
      if (c >>> i) % 2 = 1 then acc.xor (Y[8 * k + i]?.getD V2.zero) else acc) V2.zero) =
      xsumB (fun i => if c.testBit i then v2N (Y[8 * k + i]?.getD V2.zero) else 0) n := by
    intro n
    induction n with
    | zero =>
      rw [List.range_zero, List.foldl_nil]
      rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, xsumB_succ, ← ih]
      have hc : ((c >>> n) % 2 = 1) ↔ c.testBit n = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
      by_cases h : c.testBit n = true
      · rw [ite_eq_left (hc.mpr h), ite_eq_left h, v2N_xorB]
      · rw [ite_eq_right (fun e => h (hc.mp e)), ite_eq_right h, Nat.xor_zero]
  exact key 8

private theorem frTable_getB (Y : Array V2) {i : Nat} (hi : i < 3584) :
    (frTable Y)[i]! = frEntry Y (i / 256) (i % 256) := by
  unfold frTable
  rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]

private theorem ff_toNatB : (0xFF : UInt64).toNat = 2 ^ 8 - 1 := rfl

private theorem frByte_eqB (Y : Array V2) {base : Nat} (w s : UInt64) (acc : V2)
    (h1 : base % 256 = 0) (h2 : base < 3584) :
    v2N (frByte (frTable Y) base w s acc) =
      v2N acc ^^^ v2N (frEntry Y (base / 256) ((w >>> s) &&& 0xFF).toNat) := by
  have hb : ((w >>> s) &&& 0xFF).toNat < 256 := by
    rw [UInt64.toNat_and, ff_toNatB, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by omega)
  unfold frByte
  rw [v2N_xorB, frTable_getB Y (by omega)]
  have e1 : (base + ((w >>> s) &&& 0xFF).toNat) / 256 = base / 256 := by omega
  have e2 : (base + ((w >>> s) &&& 0xFF).toNat) % 256 = ((w >>> s) &&& 0xFF).toNat := by omega
  rw [e1, e2]

private theorem byte_loB (v : V2) (s : UInt64) (hs : s.toNat ≤ 56) :
    ((v.lo >>> s) &&& 0xFF).toNat = (v2N v >>> s.toNat) % 2 ^ 8 := by
  rw [UInt64.toNat_and, ff_toNatB, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt (by omega : s.toNat < 64)]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, v2N_testBitB]
  by_cases hj : j < 8
  · have : s.toNat + j < 64 := by omega
    simp [hj, this]
  · simp [hj]

private theorem byte_hiB (v : V2) (s : UInt64) (hs : s.toNat ≤ 40) :
    ((v.hi >>> s) &&& 0xFF).toNat = (v2N v >>> (64 + s.toNat)) % 2 ^ 8 := by
  rw [UInt64.toNat_and, ff_toNatB, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt (by omega : s.toNat < 64)]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, v2N_testBitB]
  have h1 : ¬ 64 + s.toNat + j < 64 := by omega
  have h2 : 64 + s.toNat + j - 64 = s.toNat + j := by omega
  rw [ite_eq_right h1, h2]

private theorem fr_coreB (Y : Array V2) (v : V2) : v2N (frApply (frTable Y) v) =
    xsumB (fun k => if (v2N v).testBit k then v2N (Y[k]?.getD V2.zero) else 0) 112 := by
  have E : ∀ q, v2N (frEntry Y q ((v2N v >>> (8 * q)) % 2 ^ 8)) =
      xsumB (fun i => if (v2N v).testBit (8 * q + i) then v2N (Y[8 * q + i]?.getD V2.zero) else 0)
        8 := by
    intro q
    rw [frEntry_v2NB]
    apply xsumB_congr
    intro i hi
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hi]
  have H : v2N (frApply (frTable Y) v) =
      xsumB (fun q => v2N (frEntry Y q ((v2N v >>> (8 * q)) % 2 ^ 8))) 14 := by
    simp (disch := decide) only [frApply, frWord6, frWord, frByte_eqB Y, byte_loB v, byte_hiB v]
    rfl
  rw [H, show (112 : Nat) = 8 * 14 from rfl, xsumB_blocks]
  exact xsumB_congr (fun q _ => E q)

private theorem ite_bit (b : Bool) (x j : Nat) :
    (if b then x else 0).testBit j = (b && x.testBit j) := by
  cases b <;> simp

private theorem fr_bit (Y : Array V2) (v : V2) (j : Nat) :
    (v2N (frApply (frTable Y) v)).testBit j =
      bx (fun k => (v2N v).testBit k && (v2N (Y[k]?.getD V2.zero)).testBit j) 112 := by
  rw [fr_coreB, xsumB_bit]
  exact bx_congr (fun k _ => ite_bit _ _ _)

private theorem testBit_of_lt_shl {M a p : Nat} (h : M < 1 <<< a) (hp : a ≤ p) :
    M.testBit p = false := by
  rw [Nat.one_shiftLeft] at h
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hp))

private theorem packFrom_bit : ∀ (l : List V2) (r p : Nat),
    (packFrom l r).testBit p =
      ((decide (r ≤ p / 128 ∧ p / 128 < r + l.length) &&
        (v2N (l.getD (p / 128 - r) V2.zero)).testBit (p % 128)) ||
      ((r + l.length) <<< 16384).testBit p)
  | [], r, p => by
    change (r <<< 16384).testBit p = _
    have h : ¬ (r ≤ p / 128 ∧ p / 128 < r + 0) := by omega
    rw [List.length_nil, decide_eq_false h, Bool.false_and, Bool.false_or, Nat.add_zero]
  | v :: l, r, p => by
    change ((v2N v <<< (128 * r)) ||| packFrom l (r + 1)).testBit p = _
    rw [Nat.testBit_or, packFrom_bit l (r + 1) p, Nat.testBit_shiftLeft, List.length_cons,
      show r + 1 + l.length = r + (l.length + 1) by omega]
    by_cases e : p / 128 = r
    · have e1 : p - 128 * r = p % 128 := by omega
      have e2 : 128 * r ≤ p := by omega
      have c1 : r ≤ p / 128 ∧ p / 128 < r + (l.length + 1) := by omega
      have c2 : ¬ (r + 1 ≤ p / 128 ∧ p / 128 < r + (l.length + 1)) := by omega
      rw [e1, decide_eq_true c1, decide_eq_false c2, e, Nat.sub_self, List.getD_cons_zero]
      simp [e2]
    · have hfirst : (decide (p ≥ 128 * r) && (v2N v).testBit (p - 128 * r)) = false := by
        by_cases e2 : 128 * r ≤ p
        · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_ltB v)
            (Nat.pow_le_pow_right (by omega) (by omega : 128 ≤ p - 128 * r)))]
          simp
        · simp [e2]
      rw [hfirst, Bool.false_or]
      by_cases c : r + 1 ≤ p / 128 ∧ p / 128 < r + (l.length + 1)
      · have c' : r ≤ p / 128 ∧ p / 128 < r + (l.length + 1) := by omega
        have ek : p / 128 - r = (p / 128 - (r + 1)) + 1 := by omega
        rw [ek, List.getD_cons_succ, decide_eq_true c, decide_eq_true c']
      · have c' : ¬ (r ≤ p / 128 ∧ p / 128 < r + (l.length + 1)) := by omega
        rw [decide_eq_false c, decide_eq_false c']
        simp

private theorem vec_mulRowsB {X Y : Array V2} (hX : WfA X) (v : V2) :
    frApply (frTable (mulRows X Y)) v = frApply (frTable Y) (frApply (frTable X) v) := by
  apply v2N_injB
  apply Nat.eq_of_testBit_eq
  intro j
  rw [fr_bit, fr_bit]
  have hL : ∀ k < 112, ((v2N v).testBit k && (v2N ((mulRows X Y)[k]?.getD V2.zero)).testBit j) =
      bx (fun l => (v2N v).testBit k && (v2N (X[k]?.getD V2.zero)).testBit l &&
        (v2N (Y[l]?.getD V2.zero)).testBit j) 112 := by
    intro k hk
    have hs : k < X.size := by rw [hX.1]; exact hk
    have hm : (mulRows X Y)[k]?.getD V2.zero = frApply (frTable Y) (X[k]?.getD V2.zero) := by
      simp [mulRows, hs]
    rw [hm, fr_bit, bx_and_left]
    exact bx_congr (fun l _ => (Bool.and_assoc _ _ _).symm)
  rw [bx_congr hL, bx_swap]
  apply bx_congr
  intro l _
  rw [fr_bit, bx_and_right]

private theorem frIdB {v : V2} (hv : v.wf = true) : frApply (frTable (idRows ())) v = v := by
  apply v2N_injB
  apply Nat.eq_of_testBit_eq
  intro j
  rw [fr_bit]
  have h : ∀ k < 112, ((v2N v).testBit k && (v2N ((idRows ())[k]?.getD V2.zero)).testBit j) =
      (((v2N v).testBit k && decide (j < 112)) && decide (k = j)) := by
    intro k hk
    have e : (idRows ())[k]?.getD V2.zero = V2.ofFn fun i => i == k := by
      simp [idRows, hk]
    rw [e, ofFn_bitsB]
    by_cases e1 : k = j
    · subst e1
      simp
    · have e2 : ¬ j = k := fun h => e1 h.symm
      simp [e1, e2]
  rw [bx_congr h, bx_single]
  by_cases hj : j < 112
  · simp [hj]
  · simp [hj, wf_bitB hv (by omega : 112 ≤ j)]

private theorem blt_bitB (m j : Nat) :
    Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)) = m.testBit j := by
  change Nat.blt 0 (m &&& 1 <<< j) = _
  have e : m &&& 1 <<< j = if m.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases e : j = i
    · subst e
      cases h : m.testBit j <;> simp [Nat.testBit_two_pow_self]
    · cases h : m.testBit j <;> simp [e, Nat.testBit_two_pow_of_ne e]
  rw [e]
  cases m.testBit j
  · rfl
  · simp only [↓reduceIte]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos j)

section Prim

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem v2N_getElem! (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2} (_hX : WfA X)
    (i : Nat) : v2N X[i]! = rowJ rm (encR X) i := by
  have hand (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
    cases a <;> cases b <;> simp [andB]
  have hk := _hK
  unfold Consts constsOK at hk
  have hk1 := ((hand _ _).mp hk).2
  have hk2 := ((hand _ _).mp hk1).2
  have hrmRaw := Nat.beq_eq.mp (((hand _ _).mp hk2).1)
  have hrm : rm = 2 ^ 112 - 1 := by
    simpa only [Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul] using hrmRaw
  have hacc (g : Nat → Nat) (l : List Nat) (z : Nat) :
      l.foldr (fun i acc => Nat.lor (g i) acc) z =
        Nat.lor (l.foldr (fun i acc => Nat.lor (g i) acc) 0) z := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, ih]
      simp only [Nat.lor_eq, Nat.or_assoc]
  have hfold (g : Nat → Nat) : ∀ n,
      (List.range n).foldr (fun i acc => Nat.lor (g i) acc) 0 =
        Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldr_append]
      change (List.range n).foldr (fun i acc => Nat.lor (g i) acc) (Nat.lor (g n) 0) =
        Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n) (g n)
      rw [show Nat.lor (g n) 0 = g n by rw [Nat.lor_eq, Nat.or_zero], hacc, ih]
  let P (u : Nat → Nat) (n : Nat) := Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (u i) (128 * i))) n
  have hbit (u : Nat → Nat) (hu : ∀ i < 112, u i < 2 ^ 128) :
      ∀ n, n ≤ 112 → ∀ j, (P u n).testBit j =
        if j < 128 * n then (u (j / 128)).testBit (j % 128) else false := by
    intro n
    induction n with
    | zero => intro _ j; simp [P]
    | succ n ih =>
      intro hn j
      change (Nat.lor (P u n) (Nat.shiftLeft (u n) (128 * n))).testBit j = _
      rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.testBit_shiftLeft,
        ih (by omega) j]
      by_cases hj : j < 128 * n
      · simp [hj, show ¬j ≥ 128 * n by omega, show j < 128 * (n + 1) by omega]
      · have hnj : 128 * n ≤ j := by omega
        by_cases hjlast : j < 128 * (n + 1)
        · have hdiv : j / 128 = n := by omega
          have hmod : j % 128 = j - 128 * n := by omega
          simp [hj, hnj, hjlast, hdiv, hmod]
        · have hlow : 128 ≤ j - 128 * n := by omega
          have hz : (u n).testBit (j - 128 * n) = false :=
            Nat.testBit_lt_two_pow ((hu n (by omega)).trans_le
              (Nat.pow_le_pow_right (by norm_num) hlow))
          simp [hj, hnj, hjlast, hz]
  have hencBit (Z : Array V2) (j : Nat) :
      (encR Z).testBit j = if j < 128 * 112 then
        (v2N (Z.getD (j / 128) V2.zero)).testBit (j % 128) else false := by
    unfold encR
    rw [hfold]
    exact hbit (fun i => v2N (Z.getD i V2.zero))
      (fun i _ => by rw [v2N_eq_toNat]; exact V2.toNat_lt _) 112 (Nat.le_refl 112) j
  have hrowwf : (X[i]!).wf = true := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    change (X[i]?.getD V2.zero).wf = true
    exact CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of _hX) i
  have hrowlt : v2N X[i]! < 2 ^ 112 := by
    rw [v2N_eq_toNat]
    exact (V2.wf_iff_toNat_lt _).mp hrowwf
  apply Nat.eq_of_testBit_eq
  intro j
  unfold rowJ
  rw [Nat.mul_eq, Nat.land_eq, Nat.testBit_and, Nat.shiftRight_eq', Nat.testBit_shiftRight,
    hrm, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 112
  · rw [show decide (j < 112) = true by simp [hj], Bool.and_true, hencBit]
    by_cases hi : i < 112
    · have hdiv : (i * 128 + j) / 128 = i := by omega
      have hmod : (i * 128 + j) % 128 = j := by omega
      have hbound : i * 128 + j < 128 * 112 := by omega
      rw [if_pos hbound, hdiv, hmod]
      rw [Array.getElem!_eq_getD]
      rfl
    · have hlarge : X.size ≤ i := by rw [_hX.1]; omega
      have hzero : X[i]! = V2.zero := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none hlarge, Option.getD_none]
        rfl
      have hbound : ¬i * 128 + j < 128 * 112 := by omega
      rw [if_neg hbound, hzero, v2N_eq_toNat]
      simp [V2.toNat, V2.zero]
  · have hle : 2 ^ 112 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show decide (j < 112) = false by simp [hj], Bool.and_false,
      Nat.testBit_lt_two_pow (hrowlt.trans_le hle)]

theorem wf_getElem! {X : Array V2} (_hX : WfA X) (i : Nat) : (X[i]!).wf = true := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  change (X[i]?.getD V2.zero).wf = true
  exact CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of _hX) i

theorem enc_ofFn (f : Nat → V2) (_hf : ∀ i < 112, (f i).wf = true) :
    WfA (Array.ofFn (n := 112) fun i => f i.val) ∧
      encR (Array.ofFn (n := 112) fun i => f i.val) = rowsJ fun i => v2N (f i) := by
  constructor
  · refine ⟨Array.size_ofFn, Array.all_eq_true.mpr ?_⟩
    intro i hi
    have hi' : i < 112 := by simpa only [Array.size_ofFn] using hi
    simpa only [Array.getElem_ofFn] using _hf i hi'
  · let X := Array.ofFn (n := 112) fun i => f i.val
    have hget (i : Nat) (hi : i < 112) : X.getD i V2.zero = f i := by
      dsimp only [X]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi,
        ↓reduceDIte, Option.getD_some]
    have hacc (g : Nat → Nat) (l : List Nat) (z : Nat) :
        l.foldr (fun i acc => Nat.lor (g i) acc) z =
          Nat.lor (l.foldr (fun i acc => Nat.lor (g i) acc) 0) z := by
      induction l with
      | nil => simp
      | cons i l ih =>
        simp only [List.foldr_cons, ih]
        simp only [Nat.lor_eq, Nat.or_assoc]
    have hfold (g : Nat → Nat) : ∀ n,
        (List.range n).foldr (fun i acc => Nat.lor (g i) acc) 0 =
          Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.range_succ, List.foldr_append]
        change (List.range n).foldr (fun i acc => Nat.lor (g i) acc) (Nat.lor (g n) 0) =
          Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n) (g n)
        rw [show Nat.lor (g n) 0 = g n by rw [Nat.lor_eq, Nat.or_zero], hacc, ih]
    unfold encR rowsJ
    rw [hfold]
    have hrec : ∀ n, n ≤ 112 →
        Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (v2N (X.getD i V2.zero)) (Nat.mul 128 i))) n =
          Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (v2N (f i)) (Nat.mul 128 i))) n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        change Nat.lor _ _ = Nat.lor _ _
        rw [ih (by omega), hget n (by omega)]
    exact hrec 112 (Nat.le_refl 112)

theorem enc_addRows {X Y : Array V2} (_hX : WfA X) (_hY : WfA Y) :
    WfA (addRows X Y) ∧ encR (addRows X Y) = Nat.xor (encR X) (encR Y) := by
  have hrepr (a : V2) : v2N a = a.toNat := by
    unfold v2N V2.toNat
    rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
      Nat.shiftLeft_eq]
    omega
  have hvxor (a b : V2) : v2N (a.xor b) = Nat.xor (v2N a) (v2N b) := by
    simp only [hrepr]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.xor_eq, Nat.testBit_xor]
    by_cases hj : j < 128
    · rw [V2.testBit_toNat (a.xor b) hj, V2.testBit_toNat a hj,
        V2.testBit_toNat b hj, V2.testBit_xor]
    · have hle : 2 ^ 128 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow ((V2.toNat_lt (a.xor b)).trans_le hle),
        Nat.testBit_lt_two_pow ((V2.toNat_lt a).trans_le hle),
        Nat.testBit_lt_two_pow ((V2.toNat_lt b).trans_le hle)]
      rfl
  let P (u : Nat → Nat) (n : Nat) := Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (u i) (128 * i))) n
  have hbit (u : Nat → Nat) (hu : ∀ i < 112, u i < 2 ^ 128) :
      ∀ n, n ≤ 112 → ∀ j, (P u n).testBit j =
        if j < 128 * n then (u (j / 128)).testBit (j % 128) else false := by
    intro n
    induction n with
    | zero => intro _ j; simp [P]
    | succ n ih =>
      intro hn j
      change (Nat.lor (P u n) (Nat.shiftLeft (u n) (128 * n))).testBit j = _
      rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.testBit_shiftLeft,
        ih (by omega) j]
      by_cases hj : j < 128 * n
      · simp [hj, show ¬j ≥ 128 * n by omega, show j < 128 * (n + 1) by omega]
      · have hnj : 128 * n ≤ j := by omega
        by_cases hjlast : j < 128 * (n + 1)
        · have hdiv : j / 128 = n := by omega
          have hmod : j % 128 = j - 128 * n := by omega
          simp [hj, hnj, hjlast, hdiv, hmod]
        · have hlow : 128 ≤ j - 128 * n := by omega
          have hz : (u n).testBit (j - 128 * n) = false :=
            Nat.testBit_lt_two_pow ((hu n (by omega)).trans_le
              (Nat.pow_le_pow_right (by norm_num) hlow))
          simp [hj, hnj, hjlast, hz]
  have hrows (u v : Nat → Nat) (hu : ∀ i < 112, u i < 2 ^ 128)
      (hv : ∀ i < 112, v i < 2 ^ 128) :
      rowsJ (fun i => Nat.xor (u i) (v i)) = Nat.xor (rowsJ u) (rowsJ v) := by
    have huv : ∀ i < 112, Nat.xor (u i) (v i) < 2 ^ 128 := by
      intro i hi
      rw [Nat.xor_eq]
      exact Nat.xor_lt_two_pow (hu i hi) (hv i hi)
    apply Nat.eq_of_testBit_eq
    intro j
    change (P (fun i => Nat.xor (u i) (v i)) 112).testBit j =
      (Nat.xor (P u 112) (P v 112)).testBit j
    rw [Nat.xor_eq, Nat.testBit_xor, hbit _ huv 112 (Nat.le_refl 112),
      hbit u hu 112 (Nat.le_refl 112), hbit v hv 112 (Nat.le_refl 112)]
    by_cases hj : j < 128 * 112
    · simp only [if_pos hj, Nat.xor_eq, Nat.testBit_xor]
    · simp [hj]
  have henc (Z : Array V2) (hZ : WfA Z) :
      encR Z = rowsJ (fun i => v2N (Z[i]?.getD V2.zero)) := by
    have hh := enc_ofFn (fun i => Z[i]?.getD V2.zero)
      (fun i _ => CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of hZ) i)
    have heq : (Array.ofFn (n := 112) fun i => Z[i.val]?.getD V2.zero) = Z := by
      apply Array.ext (by simpa only [Array.size_ofFn] using hZ.1.symm)
      intro i hi hj
      simp only [Array.getElem_ofFn, Array.getElem?_eq_getElem hj, Option.getD_some]
    simpa only [heq] using hh.2
  have hh := enc_ofFn (fun i => (X[i]?.getD V2.zero).xor (Y[i]?.getD V2.zero))
    (fun i _ => V2.xor_wf
      (CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of _hX) i)
      (CFSG.Sporadic.J4.rows_getD_wf (rows_wf_of _hY) i))
  constructor
  · change WfA (Array.ofFn (n := 112) fun i =>
      (X[i.val]?.getD V2.zero).xor (Y[i.val]?.getD V2.zero))
    exact hh.1
  · change encR (Array.ofFn (n := 112) fun i =>
      (X[i.val]?.getD V2.zero).xor (Y[i.val]?.getD V2.zero)) = _
    rw [hh.2, henc X _hX, henc Y _hY]
    simp only [hvxor]
    apply hrows
    · intro i _
      rw [hrepr]
      exact V2.toNat_lt _
    · intro i _
      rw [hrepr]
      exact V2.toNat_lt _

theorem v2N_xor (a b : V2) : v2N (a.xor b) = Nat.xor (v2N a) (v2N b) := by
  simp only [v2N_eq_toNat]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.xor_eq, Nat.testBit_xor]
  by_cases hj : j < 128
  · rw [V2.testBit_toNat (a.xor b) hj, V2.testBit_toNat a hj,
      V2.testBit_toNat b hj, V2.testBit_xor]
  · have hle : 2 ^ 128 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow ((V2.toNat_lt (a.xor b)).trans_le hle),
      Nat.testBit_lt_two_pow ((V2.toNat_lt a).trans_le hle),
      Nat.testBit_lt_two_pow ((V2.toNat_lt b).trans_le hle)]
    rfl

theorem wf_xor {a b : V2} (_ha : a.wf = true) (_hb : b.wf = true) : (a.xor b).wf = true := by
  exact CFSG.Sporadic.J4.Native.V2.xor_wf _ha _hb

theorem testBit_v2N (a : V2) {j : Nat} (_hj : j < 128) : a.testBit j = (v2N a).testBit j := by
  rw [v2N_eq_toNat, V2.testBit_toNat a _hj]

theorem wf_of_lt {v : V2} (_h : v2N v < 2 ^ 112) : v.wf = true := by
  apply (V2.wf_iff_toNat_lt v).2
  rwa [← v2N_eq_toNat]

theorem packOK_sound (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2} {M : Nat}
    (_h : packOK M X.toList = true) (_hc : canonJ pad M = true) : WfA X ∧ encR X = M := by
  unfold packOK at _h
  rw [andB_eq, Bool.and_eq_true] at _h
  obtain ⟨hp, hl⟩ := _h
  have hP := Nat.eq_of_beq_eq_true hp
  have Mhi : ∀ p, 14336 ≤ p → M.testBit p = false := by
    intro p hp
    unfold canonJ at _hc
    rw [andB_eq, Bool.and_eq_true] at _hc
    have hM : M < Nat.shiftLeft 1 14336 := Nat.le_of_ble_eq_true _hc.1
    change M < 1 <<< 14336 at hM
    exact testBit_of_lt_shl hM hp
  have hrow : ∀ (l : List V2), List.rec (motive := fun _ => Bool) true
      (fun v _ ih => andB (Nat.blt (v2N v) (Nat.shiftLeft (nat_lit 1) (nat_lit 112))) ih) l = true →
      ∀ v ∈ l, v2N v < 2 ^ 112 := by
    intro l
    induction l with
    | nil => intro _ v hv; simp at hv
    | cons a l ih =>
      intro h v hv
      change andB _ _ = true at h
      rw [andB_eq, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hv with rfl | hv
      · have : v2N v < Nat.shiftLeft 1 112 := Nat.le_of_ble_eq_true h.1
        have e : Nat.shiftLeft 1 112 = 2 ^ 112 := rfl
        rw [e] at this
        exact this
      · exact ih h.2 v hv
  have B : ∀ p, ((decide (0 ≤ p / 128 ∧ p / 128 < 0 + X.toList.length) &&
      (v2N (X.toList.getD (p / 128 - 0) V2.zero)).testBit (p % 128)) ||
      ((0 + X.toList.length) <<< 16384).testBit p) =
      (M.testBit p || (112 <<< 16384).testBit p) := by
    intro p
    have := congrArg (fun x => x.testBit p) hP
    simp only at this
    rw [packFrom_bit] at this
    rw [this]
    change (M ||| 112 <<< 16384).testBit p = _
    rw [Nat.testBit_or]
  simp only [Nat.zero_add, Nat.sub_zero, Nat.zero_le, true_and] at B
  have hlen : X.toList.length < 128 := by
    by_contra hc
    obtain ⟨q, hq, hb⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow
      (by omega : X.toList.length ≥ 2 ^ 7)
    have := B (16384 + q)
    rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Mhi _ (by omega),
      show 16384 + q - 16384 = q by omega, hb,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 112 < 2 ^ 7)
        (Nat.pow_le_pow_right (by omega) hq))] at this
    simp at this
  have hlen' : X.toList.length = 112 := by
    apply Nat.eq_of_testBit_eq
    intro q
    have := B (16384 + q)
    have h1 : ¬ (16384 + q) / 128 < X.toList.length := by omega
    rw [decide_eq_false h1, Bool.false_and, Bool.false_or, Mhi _ (by omega), Bool.false_or,
      Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, show 16384 + q - 16384 = q by omega] at this
    simpa using this
  have hs : X.size = 112 := by rw [← Array.length_toList]; exact hlen'
  refine ⟨⟨hs, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    exact wf_of_lt (hrow _ hl _ (Array.getElem_mem_toList hi))
  · apply Nat.eq_of_testBit_eq
    intro p
    rw [encR_bitB]
    by_cases hp16 : p < 16384
    · have := B p
      rw [hlen'] at this
      simp only [Nat.testBit_shiftLeft] at this
      have h1 : ¬ p ≥ 16384 := by omega
      simp only [h1, decide_false, Bool.false_and, Bool.or_false] at this
      rw [← this, List.getD_eq_getElem?_getD, Array.getElem?_toList]
    · have h1 : ¬ p / 128 < 112 := by omega
      rw [Mhi p (by omega)]
      simp [h1]

theorem beq_v2N (a b : V2) : a.beq b = Nat.beq (v2N a) (v2N b) := by
  rw [Bool.eq_iff_iff, V2.beq_iff, Nat.beq_eq]
  simp only [v2N_eq_toNat]
  exact V2.toNat_injective.eq_iff.symm

private theorem vecEtaFrom_cons (rm M : Nat) (L : List Nat) (m j x : Nat) :
    vecEtaFrom rm (M :: L) m j x = Bool.rec (motive := fun _ => Nat) (vecEtaFrom rm L m (j + 1) x)
      (CFSG.KC.Loop.strictN (vecJ rm x M) (vecEtaFrom rm L m (j + 1)))
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j))) := rfl

private theorem eta_vecB (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (T : Array (Array V2))
    (m : Nat) : ∀ (L : List Nat) (j : Nat) (acc : Array V2), WfA acc →
      (∀ i < L.length, WfA (T[j + i]?.getD (idRows ())) ∧
        encR (T[j + i]?.getD (idRows ())) = getN one L i) →
      ∀ (v : V2), v.wf = true →
      (frApply (frTable ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          mulRows acc (T[j]?.getD (idRows ())) else acc) acc)) v).wf = true ∧
        v2N (frApply (frTable ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          mulRows acc (T[j]?.getD (idRows ())) else acc) acc)) v) =
          vecEtaFrom rm L m j (v2N (frApply (frTable acc) v))
  | [], _, acc, h, _, v, _ => ⟨wf_frApply h v, rfl⟩
  | M :: L, j, acc, h, hT, v, hv => by
    have h0 := hT 0 (by simp)
    rw [Nat.add_zero] at h0
    have hT' : ∀ i < L.length, WfA (T[j + 1 + i]?.getD (idRows ())) ∧
        encR (T[j + 1 + i]?.getD (idRows ())) = getN one L i := by
      intro i hi
      have := hT (i + 1) (by simp; omega)
      rw [show j + (i + 1) = j + 1 + i by omega] at this
      exact this
    rw [List.length_cons, List.range'_succ, List.foldl_cons, vecEtaFrom_cons, blt_bitB]
    by_cases hb : m.testBit j
    · simp only [hb, ↓reduceIte]
      have ih := eta_vecB hK T m L (j + 1) _ (wf_mulRows h h0.1) hT' v hv
      rw [vec_mulRowsB h, v2N_frApply hK h0.1 (wf_frApply h v), h0.2] at ih
      refine ⟨ih.1, ?_⟩
      rw [ih.2]
      exact (strictN_eq _ _).symm
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact eta_vecB hK T m L (j + 1) acc h hT' v hv

theorem v2N_etaRows (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    {Ts : List Nat}
    (_hT : ∀ j < Ts.length, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one Ts j)
    {v : V2} (_hv : v.wf = true) (m : Nat) :
    (frApply (frTable (CFSG.Sporadic.J4.QT.etaRows T Ts.length m)) v).wf = true ∧
      v2N (frApply (frTable (CFSG.Sporadic.J4.QT.etaRows T Ts.length m)) v) =
        vecEtaK rm Ts m (v2N v) := by
  have h := eta_vecB _hK T m Ts 0 (idRows ()) wf_idRows (fun i hi => by
    rw [Nat.zero_add]
    exact _hT i hi) v _hv
  rw [frIdB _hv] at h
  unfold CFSG.Sporadic.J4.QT.etaRows vecEtaK
  rw [List.range_eq_range']
  exact h

theorem vec_mulRows {X Y : Array V2} (_hX : WfA X) (_hY : WfA Y) {v : V2} (_hv : v.wf = true) :
    frApply (frTable (mulRows X Y)) v = frApply (frTable Y) (frApply (frTable X) v) := by
  apply V2.eq_of_toVec_eq
    (wf_frApply (wf_mulRows _hX _hY) v)
    (wf_frApply _hY (frApply (frTable X) v))
  rw [CFSG.Sporadic.J4.frApply_toVec_eq_vecMul,
    CFSG.Sporadic.J4.rowsMatrix_mulRows,
    CFSG.Sporadic.J4.frApply_toVec_eq_vecMul,
    CFSG.Sporadic.J4.frApply_toVec_eq_vecMul,
    Matrix.vecMul_vecMul]

theorem v2N_etaVec (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)}
    {Ts : List Nat}
    (_hT : ∀ j < Ts.length, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one Ts j)
    (_hs : T.size = Ts.length) (_hw : CFSG.Sporadic.J4.QT.w0.wf = true) (m : Nat) :
    (CFSG.Sporadic.J4.QT.etaVec (T.map frTable) Ts.length m).wf = true ∧
      v2N (CFSG.Sporadic.J4.QT.etaVec (T.map frTable) Ts.length m) =
        vecEtaK rm Ts m (v2N CFSG.Sporadic.J4.QT.w0) := by
  have key : ∀ (L : List Nat) (j : Nat) (x : V2), x.wf = true → j + L.length ≤ T.size →
      (∀ i < L.length, WfA (T[j + i]?.getD (idRows ())) ∧
        encR (T[j + i]?.getD (idRows ())) = getN one L i) →
      ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          frApply ((T.map frTable)[j]?.getD #[]) acc else acc) x).wf = true ∧
        v2N ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          frApply ((T.map frTable)[j]?.getD #[]) acc else acc) x) = vecEtaFrom rm L m j (v2N x) := by
    intro L
    induction L with
    | nil => intro j x hx _ _; exact ⟨hx, rfl⟩
    | cons M L ih =>
      intro j x hx hle hT
      have h0 := hT 0 (by simp)
      rw [Nat.add_zero] at h0
      have hT' : ∀ i < L.length, WfA (T[j + 1 + i]?.getD (idRows ())) ∧
          encR (T[j + 1 + i]?.getD (idRows ())) = getN one L i := by
        intro i hi
        have := hT (i + 1) (by simp; omega)
        rw [show j + (i + 1) = j + 1 + i by omega] at this
        exact this
      have hle' : j + 1 + L.length ≤ T.size := by simp at hle; omega
      have hjs : j < T.size := by simp at hle; omega
      have htab : (T.map frTable)[j]?.getD #[] = frTable (T[j]?.getD (idRows ())) := by
        rw [Array.getElem?_map, getElem?_pos T j hjs, Option.map_some, Option.getD_some,
          Option.getD_some]
      rw [List.length_cons, List.range'_succ, List.foldl_cons, vecEtaFrom_cons, blt_bitB]
      by_cases hb : m.testBit j
      · simp only [hb, ↓reduceIte]
        rw [htab]
        have ih' := ih (j + 1) _ (wf_frApply h0.1 x) hle' hT'
        rw [v2N_frApply _hK h0.1 hx, h0.2] at ih'
        refine ⟨ih'.1, ?_⟩
        rw [ih'.2]
        exact (strictN_eq _ _).symm
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact ih (j + 1) x hx hle' hT'
  have h := key Ts 0 _ _hw (by omega) (fun i hi => by
    rw [Nat.zero_add]
    exact _hT i hi)
  unfold CFSG.Sporadic.J4.QT.etaVec vecEtaK
  rw [List.range_eq_range']
  exact h

theorem triOK_of (vs : Array V2) (ps : Array Nat) (_h : triK (vs.toList.map v2N) ps.toList = true) :
    CFSG.Sporadic.J4.QT.triOK vs ps = true := by
  have hget (d : Nat) (l : List Nat) : ∀ i, getN d l i = l.getD i d := by
    induction l with
    | nil => intro i; rfl
    | cons x xs ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i => exact ih i
  have hall (n : Nat) (f : Nat → Bool) :
      allR n f = true → ∀ i < n, f i = true := by
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro h i hi
      change andB (allR n f) (f n) = true at h
      rw [andB_eq, Bool.and_eq_true] at h
      by_cases hin : i < n
      · exact ih h.1 i hin
      · have he : i = n := by omega
        subst i
        exact h.2
  have hnot (b : Bool) : notB b = !b := by cases b <;> rfl
  have hvget (k : Nat) (hk : k < vs.size) :
      getN 0 (vs.toList.map v2N) k = v2N vs[k]! := by
    rw [hget]
    simp [List.getD_eq_getElem?_getD, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, hk]
  have hpget (k : Nat) (hk : k < ps.size) : getN 0 ps.toList k = ps[k]! := by
    rw [hget]
    simp [List.getD_eq_getElem?_getD, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?, hk]
  unfold triK at _h
  rw [andB_eq, Bool.and_eq_true] at _h
  have hs : vs.size = ps.size := by
    have he := Nat.beq_eq.mp _h.1
    simpa using he
  have hrow (k : Nat) (hk : k < vs.size) :
      v2N vs[k]! < 2 ^ 112 ∧ ps[k]! < 112 ∧
        bitB (v2N vs[k]!) ps[k]! = true ∧
        ∀ j < k, notB (bitB (v2N vs[k]!) ps[j]!) = true := by
    have h := hall _ _ _h.2 k (by simpa using hk)
    rw [hvget k hk, hpget k (by omega)] at h
    simp only [andB_eq, Bool.and_eq_true] at h
    have hv : v2N vs[k]! < 2 ^ 112 := by
      have hv := Nat.le_of_ble_eq_true h.1
      have hle : (v2N vs[k]!).succ ≤ 2 ^ 112 := by
        simpa only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul] using hv
      exact Nat.lt_of_succ_le hle
    have hp : ps[k]! < 112 := Nat.le_of_ble_eq_true h.2.1
    refine ⟨hv, hp, h.2.2.1, ?_⟩
    intro j hj
    have hclear := hall _ _ h.2.2.2 j hj
    simpa only [hpget j (by omega)] using hclear
  unfold CFSG.Sporadic.J4.QT.triOK
  rw [Bool.and_eq_true]
  refine ⟨by simpa only [beq_iff_eq] using hs, List.all_eq_true.mpr ?_⟩
  intro k hk
  have hks : k < vs.size := List.mem_range.mp hk
  obtain ⟨hv, hp, hset, hprev⟩ := hrow k hks
  have hw : (vs[k]!).wf = true := wf_of_lt hv
  have hb : (vs[k]!).testBit ps[k]! = true := by
    rw [testBit_v2N _ (by omega), ← bitB_eq]
    exact hset
  have hprevious : (List.range k).all (fun j => !((vs[k]!).testBit ps[j]!)) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    have hjk : j < k := List.mem_range.mp hj
    have hpj : ps[j]! < 112 := (hrow j (by omega)).2.1
    rw [← hnot, testBit_v2N _ (by omega), ← bitB_eq]
    exact hprev j hjk
  simp only [hw, hp, decide_true, hb, hprevious, Bool.true_and]

end Prim

theorem notB_eq (b : Bool) : notB b = !b := by cases b <;> rfl

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allR_eq (f : Nat → Bool) : ∀ n, allR n f = (List.range n).all f
  | 0 => rfl
  | n + 1 => by
    change andB (allR n f) (f n) = _
    rw [allR_eq f n, andB_eq, List.range_succ, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true]

theorem all_range_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).all f = (List.range n).all g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.all_append, List.all_append,
      all_range_congr fun i hi => h i (Nat.lt_succ_of_lt hi), List.all_cons, List.all_cons,
      h n (Nat.lt_succ_self n), List.all_nil, List.all_nil]

theorem allR_spec {n : Nat} {f : Nat → Bool} (h : allR n f = true) : ∀ i < n, f i = true := by
  intro i hi
  rw [allR_eq, List.all_eq_true] at h
  exact h i (List.mem_range.2 hi)

theorem rec_rows_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 128 i))) n =
      Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (g i) (Nat.mul 128 i))) n
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.lor (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 128 i))) n) _ =
      Nat.lor (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => Nat.lor acc (Nat.shiftLeft (g i) (Nat.mul 128 i))) n) _
    rw [rec_rows_congr fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)]

theorem rowsJ_congr {f g : Nat → Nat} (h : ∀ i < 112, f i = g i) : rowsJ f = rowsJ g :=
  rec_rows_congr h

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem inWB_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {P : Nat}
    (hP : WfA pRows ∧ encR pRows = P) {x : V2} (hx : x.wf = true) :
    inWB x = inWBK rm P (v2N x) := by
  unfold inWB inWBK
  simp only []
  rw [strictB_eq, allR_eq, ← hP.2, ← v2N_frApply hK hP.1 hx]
  apply all_range_congr
  intro t ht
  rw [notB_eq, bitB_eq, testBit_v2N _ (by omega)]
  rfl

theorem trivOnComp_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {P : Nat}
    (hP : WfA pRows ∧ encR pRows = P) {cv : List Nat}
    (hcv : ∀ j < 12, (compV[j]!).wf = true ∧ v2N compV[j]! = getN 0 cv j) {X : Array V2}
    (hX : WfA X) : trivOnComp X = trivK rm P cv (encR X) := by
  unfold trivOnComp trivK
  simp only []
  rw [allR_eq]
  apply all_range_congr
  intro j hj
  obtain ⟨hw, hv⟩ := hcv j hj
  rw [inWB_eq hK hP (wf_xor (wf_frApply hX _) hw), v2N_xor, v2N_frApply hK hX hw, hv]

theorem id_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    WfA (idRows ()) ∧ encR (idRows ()) = one :=
  ⟨wf_idRows, enc_idRows hK⟩

theorem mul_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array V2} {x y : Nat}
    (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y) :
    WfA (mulRows X Y) ∧ encR (mulRows X Y) = mulJ c rm x y :=
  ⟨wf_mulRows hX.1 hY.1, by rw [enc_mulRows hK hX.1 hY.1, hX.2, hY.2]⟩

theorem pow_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2} {x : Nat}
    (hX : WfA X ∧ encR X = x) (e : Nat) :
    WfA (powRows X e) ∧ encR (powRows X e) = powJ c rm one x e :=
  ⟨wf_powRows hX.1 e, by rw [enc_powRows hK hX.1, hX.2]⟩

theorem eqRows_of {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y) :
    eqRows X Y = Nat.beq x y := by
  rw [eqRows_eq hX.1 hY.1, hX.2, hY.2]

theorem cmz_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Z : Nat}
    (hz : WfA (zR ()) ∧ encR (zR ()) = Z) {X : Array V2} (hX : WfA X) :
    cmz X = Nat.beq (mulJ c rm (encR X) Z) (mulJ c rm Z (encR X)) := by
  unfold cmz
  rw [eqRows_eq (wf_mulRows hX hz.1) (wf_mulRows hz.1 hX), enc_mulRows hK hX hz.1,
    enc_mulRows hK hz.1 hX, hz.2]

end CFSG.KC.J4Q

end
