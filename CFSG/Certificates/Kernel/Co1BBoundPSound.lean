module

public import Certificates.Data.Kernel.Co1BBoundP

public section

universe u

namespace CFSG.KC.Co1BBoundP

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.Co1BBound CFSG.KC.Co1BBoundN

theorem strictT_eq {α : Sort u} (y : Nat) (k : Nat → α) : strictT y k = k y := by
  cases y <;> rfl

@[expose] def fd24 (X k : Nat) : Nat := X / 2 ^ (24 * k) % 2 ^ 24

theorem pg_eq (X k : Nat) :
    CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) X k = fd24 X k := by
  unfold CFSG.KC.Enum.pg CFSG.KS.mask fd24
  change (X >>> (24 * k)) &&& ((1 <<< 24) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_fd24 (X k i : Nat) :
    (fd24 X k).testBit i = (decide (i < 24) && X.testBit (24 * k + i)) := by
  unfold fd24
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]

theorem fd24_xor (a b k : Nat) : fd24 (a ^^^ b) k = fd24 a k ^^^ fd24 b k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_fd24, testBit_fd24, testBit_fd24, Nat.testBit_xor]
  cases decide (i < 24) <;> rfl

theorem fd24_land (a b k : Nat) : fd24 (a &&& b) k = fd24 a k &&& fd24 b k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_fd24, testBit_fd24, testBit_fd24, Nat.testBit_and]
  cases decide (i < 24) <;> simp

theorem fd24_zero_left (k : Nat) : fd24 0 k = 0 := by
  simp [fd24]

theorem fd24_zero (X : Nat) : fd24 X 0 = X % 2 ^ 24 := by
  simp [fd24]

theorem fd24_succ (X k : Nat) : fd24 X (k + 1) = fd24 (X / 2 ^ 24) k := by
  unfold fd24
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ, Nat.add_comm (24 * k)]

theorem fd24_cons_zero {a : Nat} (ha : a < 2 ^ 24) (Y : Nat) : fd24 (2 ^ 24 * Y + a) 0 = a := by
  rw [fd24_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

theorem fd24_cons_succ {a : Nat} (ha : a < 2 ^ 24) (Y k : Nat) :
    fd24 (2 ^ 24 * Y + a) (k + 1) = fd24 Y k := by
  rw [fd24_succ, Nat.mul_add_div (Nat.two_pow_pos 24), Nat.div_eq_of_lt ha, Nat.add_zero]

theorem fd24_mul {r : Nat} (hr : r < 2 ^ 24) :
    ∀ (k X : Nat), (∀ j, fd24 X j ≤ 1) → fd24 (X * r) k = fd24 X k * r := by
  intro k
  induction k with
  | zero =>
    intro X hX
    have h0 := hX 0
    rw [fd24_zero] at h0
    rw [fd24_zero, fd24_zero, Nat.mul_mod, Nat.mod_eq_of_lt hr]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h0 with h | h <;> rw [h] <;> simp [Nat.mod_eq_of_lt hr]
  | succ k ih =>
    intro X hX
    have h0 := hX 0
    rw [fd24_zero] at h0
    have hm : X % 2 ^ 24 * r < 2 ^ 24 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h0 with h | h <;> rw [h] <;> simp [hr]
    have e : X * r = 2 ^ 24 * (X / 2 ^ 24 * r) + X % 2 ^ 24 * r := by
      rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.div_add_mod X (2 ^ 24)]
    rw [e, fd24_cons_succ hm, ih _ (fun j => by rw [← fd24_succ]; exact hX _), fd24_succ]

theorem onesN_succ (n : Nat) : onesN (n + 1) = 2 ^ 24 * onesN n + 1 := by
  change (onesN n <<< 24) ||| 1 = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by decide : 1 < 2 ^ 24), Nat.shiftLeft_eq, Nat.mul_comm]

theorem fd24_onesN : ∀ n k, fd24 (onesN n) k = if k < n then 1 else 0 := by
  intro n
  induction n with
  | zero => intro k; exact fd24_zero_left k
  | succ n ih =>
    intro k
    rw [onesN_succ]
    cases k with
    | zero => rw [fd24_cons_zero (by decide)]; simp
    | succ k => rw [fd24_cons_succ (by decide), ih]; simp

theorem land_one (x : Nat) : x &&& 1 = if x.testBit 0 then 1 else 0 := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h]

theorem bit_eq (X j : Nat) : bit X j = X.testBit j := by
  unfold bit
  change Nat.beq ((X >>> j) &&& 1) 1 = _
  rw [land_one, Nat.testBit_shiftRight, Nat.add_zero]
  cases X.testBit j <;> rfl

theorem rowF_lt (T j : Nat) : rowF (nat_lit 24) T j < 2 ^ 24 := by
  unfold rowF fget maskN pw2
  change (T >>> (j * 24)) &&& ((1 <<< 24) - 1) < 2 ^ 24
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos 24)

theorem fd24_bitP {k : Nat} (hk : k < 840) {j : Nat} (hj : j < 24) (P : Nat) :
    fd24 ((P >>> j) &&& ONES) k = if (fd24 P k).testBit j then 1 else 0 := by
  rw [fd24_land]
  change fd24 (P >>> j) k &&& fd24 (onesN 840) k = _
  rw [fd24_onesN, if_pos hk, land_one, testBit_fd24, testBit_fd24, Nat.testBit_shiftRight]
  simp [hj, Nat.add_comm j]

theorem fd24_bitP_le (j P k : Nat) : fd24 ((P >>> j) &&& ONES) k ≤ 1 := by
  rw [fd24_land]
  change fd24 (P >>> j) k &&& fd24 (onesN 840) k ≤ 1
  rw [fd24_onesN]
  split
  · exact Nat.and_le_right
  · simp

theorem vmP_aux (T P : Nat) {k : Nat} (hk : k < 840) : ∀ n, n ≤ 24 →
    fd24 (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => ((P >>> j) &&& ONES) * rowF (nat_lit 24) T j ^^^ acc) n) k =
    Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (rowF (nat_lit 24) T j ^^^ acc) (bit (fd24 P k) j))
      n := by
  intro n
  induction n with
  | zero => intro _; exact fd24_zero_left k
  | succ n ih =>
    intro hn
    change fd24 (((P >>> n) &&& ONES) * rowF (nat_lit 24) T n ^^^ Nat.rec (motive := fun _ => Nat) 0
        (fun j acc => ((P >>> j) &&& ONES) * rowF (nat_lit 24) T j ^^^ acc) n) k =
      Bool.rec (motive := fun _ => Nat)
        (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Bool.rec (motive := fun _ => Nat) acc
          (rowF (nat_lit 24) T j ^^^ acc) (bit (fd24 P k) j)) n)
        (rowF (nat_lit 24) T n ^^^ Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
          Bool.rec (motive := fun _ => Nat) acc (rowF (nat_lit 24) T j ^^^ acc) (bit (fd24 P k) j)) n)
        (bit (fd24 P k) n)
    rw [fd24_xor, fd24_mul (rowF_lt T n) k _ (fd24_bitP_le n P), fd24_bitP hk (by omega), ih (by omega),
      bit_eq]
    cases (fd24 P k).testBit n
    · simp
    · simp

theorem pg_vmP (T P : Nat) {k : Nat} (hk : k < 840) :
    CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (vmP ONES T P) k =
      vmF (nat_lit 24) T (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k) := by
  rw [pg_eq, pg_eq]
  exact vmP_aux T P hk 24 (Nat.le_refl 24)

theorem fd24_vmPn (nb : Nat) (TL : List Nat) (a P : Nat) {k : Nat} (hk : k < 840) :
    fd24 (vmPn nb ONES TL a P) k = vmTn nb TL a (fd24 P k) := by
  unfold vmPn vmTn
  cases Nat.blt a nb
  · exact fd24_zero_left k
  · have := pg_vmP (getL 0 TL a) P hk
    rw [pg_eq, pg_eq] at this
    exact this

theorem foldl_xor_left (g : Nat → Nat) : ∀ (S : List Nat) (u A : Nat),
    S.foldl (fun acc a => acc ^^^ g a) (u ^^^ A) = u ^^^ S.foldl (fun acc a => acc ^^^ g a) A
  | [], _, _ => rfl
  | a :: S, u, A => by
    rw [List.foldl_cons, List.foldl_cons, Nat.xor_assoc]
    exact foldl_xor_left g S u _

theorem fd24_sumP_aux (nb : Nat) (TL : List Nat) (P : Nat) {k : Nat} (hk : k < 840) :
    ∀ (S : List Nat) (A : Nat),
    fd24 (S.foldl (fun acc a => acc ^^^ vmPn nb ONES TL a P) A) k =
      S.foldl (fun acc a => acc ^^^ vmTn nb TL a (fd24 P k)) (fd24 A k)
  | [], _ => rfl
  | a :: S, A => by
    rw [List.foldl_cons, List.foldl_cons, fd24_sumP_aux nb TL P hk S, fd24_xor, fd24_vmPn nb TL a P hk]

theorem xor_sumP (nb : Nat) (TL S : List Nat) (fv P : Nat) {k : Nat} (hk : k < 840) :
    Nat.xor fv (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (sumP nb ONES TL S P) k) =
      combKn nb TL S fv (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k) := by
  rw [pg_eq, pg_eq]
  change fv ^^^ fd24 (S.foldl (fun acc a => acc ^^^ vmPn nb ONES TL a P) 0) k =
    S.foldl (fun acc a => acc ^^^ vmTn nb TL a (fd24 P k)) fv
  rw [fd24_sumP_aux nb TL P hk, fd24_zero_left, ← foldl_xor_left, Nat.xor_zero]

theorem packP_eq (nb O : Nat) (TL : List Nat) (P : Nat) : ∀ (CP : List (List Nat))
    (kont : List (Nat × Nat × Nat) → Nat),
    packP nb O TL P CP kont = kont (CP.map fun c => (c.headD 0, c.tail.headD 0, sumP nb O TL c.tail.tail P))
  | [], _ => rfl
  | c :: CP, kont => by
    change strictT (sumP nb O TL c.tail.tail P)
      (fun Q => packP nb O TL P CP fun L => kont ((c.headD 0, c.tail.headD 0, Q) :: L)) = _
    rw [strictT_eq, packP_eq nb O TL P CP]
    rfl

theorem condsQ_pack (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (P : Nat) {k : Nat} (hk : k < 840) :
    ∀ CP : List (List Nat),
    condsQ XB (CP.map fun c => (c.headD 0, c.tail.headD 0, sumP nb ONES TL c.tail.tail P)) k =
      condsKn nb XB TL CP (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)
  | [] => rfl
  | c :: CP => by
    change andB (Nat.beq (typK XB (Nat.xor (c.tail.headD 0)
        (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (sumP nb ONES TL c.tail.tail P) k)))
        (c.headD 0)) (condsQ XB (CP.map fun c => (c.headD 0, c.tail.headD 0, sumP nb ONES TL c.tail.tail P)) k) =
      andB (condKn nb XB TL (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k) c)
        (condsKn nb XB TL CP (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k))
    rw [condsQ_pack nb XB TL P hk CP, xor_sumP nb TL _ _ P hk]
    rfl

theorem condsKn_append (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (CR : List (List Nat)) (x : Nat) :
    ∀ CP : List (List Nat),
    condsKn nb XB TL (CP ++ CR) x = andB (condsKn nb XB TL CP x) (condsKn nb XB TL CR x)
  | [] => rfl
  | c :: CP => by
    change andB (condKn nb XB TL x c) (condsKn nb XB TL (CP ++ CR) x) =
      andB (andB (condKn nb XB TL x c) (condsKn nb XB TL CP x)) (condsKn nb XB TL CR x)
    rw [condsKn_append nb XB TL CR x CP]
    cases condKn nb XB TL x c <;> rfl

theorem cnt_congr (z : Nat) (q q' : Nat → Bool) : ∀ n, (∀ k < n, q k = q' k) →
    Nat.rec (motive := fun _ => Nat) z (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (q k)) n =
      Nat.rec (motive := fun _ => Nat) z
        (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (q' k)) n
  | 0, _ => rfl
  | n + 1, h => by
    have e := congr (congrArg (fun (a : Nat) (b : Bool) => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) b)
      (cnt_congr z q q' n (fun k hk => h k (by omega)))) (h n (by omega))
    exact e

theorem cntChunkP_aux (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (CP CR : List (List Nat)) (P : Nat)
    (N : Nat) (hN : N ≤ 840) :
    packP nb ONES TL P CP (fun QS =>
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
          (andB (condsQ XB QS k)
            (condsKn nb XB TL CR (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)))) N) =
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => (fun v => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
        (condsKn nb XB TL (CP ++ CR) v)) (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) N := by
  rw [packP_eq]
  exact cnt_congr (nat_lit 0)
    (fun k => andB (condsQ XB (CP.map fun c => (c.headD 0, c.tail.headD 0, sumP nb ONES TL c.tail.tail P)) k)
      (condsKn nb XB TL CR (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)))
    (fun k => condsKn nb XB TL (CP ++ CR) (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k))
    N fun k hk => by
      rw [condsQ_pack nb XB TL P (by omega), condsKn_append]

theorem cntChunkP_eq (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (CP CR : List (List Nat)) (P : Nat) :
    cntChunkP nb XB TL ONES CP CR P = cntChunkK (condsKn nb XB TL (CP ++ CR)) P :=
  cntChunkP_aux nb XB TL CP CR P (nat_lit 840) (Nat.le_refl 840)

theorem cntTabP_eq (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (CP CR : List (List Nat))
    (F : Nat → Nat) (a m : Nat) :
    cntTabP nb XB TL CP CR F a m = cntTabK (condsKn nb XB TL (CP ++ CR)) F a m := by
  unfold cntTabP cntTabK
  rw [strictT_eq]
  congr 1
  funext j acc
  rw [strictT_eq, cntChunkP_eq]

theorem lvlChunkP_eq (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (CF : List (List (List Nat)))
    (NP : List Nat) (F : Nat → Nat) (CN : List (List Nat)) (n : Nat) :
    lvlChunkP nb XB TL CF NP F CN n = lvlChunkKn nb XB TL CF F CN n := by
  unfold lvlChunkP lvlChunkKn
  rw [cntTabP_eq, List.take_append_drop]

theorem length_filter_le_of_imp {α : Type u} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ X : List α, (X.filter p).length ≤ (X.filter q).length
  | [] => Nat.le_refl 0
  | x :: X => by
    have ih := length_filter_le_of_imp p q h X
    rw [List.filter_cons, List.filter_cons]
    cases hp : p x
    · cases q x
      · simpa using ih
      · simp only [if_true, if_false, List.length_cons, Bool.false_eq_true]
        omega
    · rw [h x hp]
      simpa using ih

theorem mem_of_mem_selC {α : Type u} {conds : List α} {sel : List Nat} {c : α}
    (h : c ∈ selC conds sel) : c ∈ conds := by
  unfold selC at h
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 h
  exact List.mem_iff_getElem?.2 ⟨i, hi⟩

theorem filter_length_le_selC {α β : Type u} (X : List α) (conds : List β) (sel : List Nat)
    (p : α → β → Bool) :
    (X.filter fun x => conds.all (p x)).length ≤ (X.filter fun x => (selC conds sel).all (p x)).length :=
  length_filter_le_of_imp _ _ (fun x h =>
    List.all_eq_true.2 fun c hc => List.all_eq_true.1 h c (mem_of_mem_selC hc)) X

end CFSG.KC.Co1BBoundP

end
