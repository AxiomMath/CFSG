module

public import Certificates.Data.Kernel.GL5B
public import CFSG.Certificates.Kernel.F4M3BSound
public import CFSG.CGT.Stroth77.Section1GL5Check
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.GL5B

open CFSG.CGT.Stroth77.GL5

theorem testBit_eq_bitB (v j : Nat) : v.testBit j = bitB v j := by
  have hs : Nat.shiftRight v j = v / 2 ^ j := Nat.shiftRight_eq_div_pow v j
  simp only [bitB, Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, hs]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h] <;> rfl

theorem ite_eq_rec (b : Bool) (m : Nat) :
    (if b = true then m else 0) = Bool.rec (motive := fun _ => Nat) 0 m b := by
  cases b <;> rfl

theorem vmF_eq (v m0 m1 m2 m3 m4 : Nat) : vmF v m0 m1 m2 m3 m4 = vm5 v m0 m1 m2 m3 m4 := by
  simp only [vmF, vm5, testBit_eq_bitB, ite_eq_rec]
  rfl

theorem mulF_eq (a b : Nat) : mulF a b = mulC a b := by
  simp only [mulF, mulC, vmF_eq]

theorem powF_eq (h : Nat) : ∀ k, powF h k = powC h k
  | 0 => rfl
  | k + 1 => by
    change mulF h (powF h k) = mulC h (powC h k)
    rw [mulF_eq, powF_eq h k]

theorem goodF_eq (h : Nat) : goodF h = good h := by
  simp only [goodF, good, mulF_eq]

theorem testBit_ite (b : Bool) (m k : Nat) :
    (if b = true then m else 0).testBit k = (b && m.testBit k) := by
  cases b <;> simp

theorem vm5_testBit (v m0 m1 m2 m3 m4 k : Nat) : (vm5 v m0 m1 m2 m3 m4).testBit k =
    (xor (xor (xor (xor (v.testBit 0 && m0.testBit k) (v.testBit 1 && m1.testBit k))
      (v.testBit 2 && m2.testBit k)) (v.testBit 3 && m3.testBit k))
      (v.testBit 4 && m4.testBit k)) := by
  simp only [vm5, Nat.testBit_xor, testBit_ite]

theorem ite_xor (b c : Bool) (m : Nat) : (if (b ^^ c) = true then m else 0) =
    (if b = true then m else 0) ^^^ (if c = true then m else 0) := by
  cases b <;> cases c <;> simp

theorem vm_xor (v w c : Nat) : vm (v ^^^ w) c = vm v c ^^^ vm w c := by
  simp only [vm, vm5, Nat.testBit_xor, ite_xor]
  ac_rfl

theorem vm_zero (c : Nat) : vm 0 c = 0 := by simp [vm, vm5]

theorem vm_ite (b : Bool) (v c : Nat) :
    vm (if b = true then v else 0) c = if b = true then vm v c else 0 := by
  cases b <;> simp [vm_zero]

theorem vm_mulC (v a b : Nat) : vm v (mulC a b) = vm (vm v b) a := by
  rw [vm, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC]
  simp only [vm5, ← vm_ite, ← vm_xor]
  rfl

theorem mulC_assoc (a b c : Nat) : mulC (mulC a b) c = mulC a (mulC b c) := by
  rw [mulC_eq, mulC_eq a (mulC b c)]
  simp only [vm_mulC, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC]

theorem vm_idC {v : Nat} (hv : v < 32) : vm v idC = v := by
  interval_cases v <;> decide

theorem idC_mulC {c : Nat} (hc : c < N) : mulC idC c = c := by
  rw [mulC_eq, vm_idC (r0_lt c), vm_idC (r1_lt c), vm_idC (r2_lt c), vm_idC (r3_lt c),
    vm_idC (r4_lt c), ofRows_rows hc]

theorem powC_add (h : Nat) : ∀ m n, powC h (m + n) = mulC (powC h m) (powC h n)
  | 0, n => by rw [Nat.zero_add]; exact (idC_mulC (powC_lt h n)).symm
  | m + 1, n => by
    rw [Nat.add_right_comm]
    change mulC h (powC h (m + n)) = mulC (mulC h (powC h m)) (powC h n)
    rw [powC_add h m n, mulC_assoc]

theorem vm_unit (c : Nat) : vm 1 c = r0 c ∧ vm 2 c = r1 c ∧ vm 4 c = r2 c ∧ vm 8 c = r3 c ∧
    vm 16 c = r4 c := by
  simp [vm, vm5, Nat.testBit]

theorem mulC_idC {c : Nat} (hc : c < N) : mulC c idC = c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := vm_unit c
  rw [mulC_eq]
  change ofRows (vm 1 c) (vm 2 c) (vm 4 c) (vm 8 c) (vm 16 c) = c
  rw [h0, h1, h2, h3, h4, ofRows_rows hc]

@[expose] def sqC (c : Nat) : Nat := mulC c c

theorem powC_64 {c : Nat} (hc : c < N) : powC c 64 = sqC (sqC (sqC (sqC (sqC (sqC c))))) := by
  have h2 : ∀ k, powC c (k + k) = sqC (powC c k) := fun k => powC_add c k k
  have h1 : powC c 1 = c := mulC_idC hc
  have e64 : (64 : Nat) = 32 + 32 := rfl
  have e32 : (32 : Nat) = 16 + 16 := rfl
  have e16 : (16 : Nat) = 8 + 8 := rfl
  have e8 : (8 : Nat) = 4 + 4 := rfl
  have e4 : (4 : Nat) = 2 + 2 := rfl
  have e2 : (2 : Nat) = 1 + 1 := rfl
  rw [e64, h2, e32, h2, e16, h2, e8, h2, e4, h2, e2, h2, h1]

variable {α β : Type}

@[expose] def R5.map (f : α → β) (r : R5 α) : R5 β := ⟨f r.e0, f r.e1, f r.e2, f r.e3, f r.e4⟩

@[expose] def M5.map (f : α → β) (A : M5 α) : M5 β :=
  ⟨A.r0.map f, A.r1.map f, A.r2.map f, A.r3.map f, A.r4.map f⟩

@[expose] noncomputable def rowD (o : Ops α) (s : R5 α) (A : M5 α) : R5 α :=
  ⟨dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e0 A.r1.e0 A.r2.e0 A.r3.e0 A.r4.e0,
    dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e1 A.r1.e1 A.r2.e1 A.r3.e1 A.r4.e1,
    dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e2 A.r1.e2 A.r2.e2 A.r3.e2 A.r4.e2,
    dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e3 A.r1.e3 A.r2.e3 A.r3.e3 A.r4.e3,
    dot o s.e0 s.e1 s.e2 s.e3 s.e4 A.r0.e4 A.r1.e4 A.r2.e4 A.r3.e4 A.r4.e4⟩

@[expose] noncomputable def mulD (o : Ops α) (A B : M5 α) : M5 α :=
  ⟨rowD o B.r0 A, rowD o B.r1 A, rowD o B.r2 A, rowD o B.r3 A, rowD o B.r4 A⟩

@[expose] noncomputable def rowCD (o : Ops α) (s : Nat) (A : M5 α) : R5 α :=
  ⟨sel o s A.r0.e0 A.r1.e0 A.r2.e0 A.r3.e0 A.r4.e0,
    sel o s A.r0.e1 A.r1.e1 A.r2.e1 A.r3.e1 A.r4.e1,
    sel o s A.r0.e2 A.r1.e2 A.r2.e2 A.r3.e2 A.r4.e2,
    sel o s A.r0.e3 A.r1.e3 A.r2.e3 A.r3.e3 A.r4.e3,
    sel o s A.r0.e4 A.r1.e4 A.r2.e4 A.r3.e4 A.r4.e4⟩

@[expose] noncomputable def mulCD (o : Ops α) (A : M5 α) (K : Nat) : M5 α :=
  ⟨rowCD o (rowN K 0) A, rowCD o (rowN K 1) A, rowCD o (rowN K 2) A, rowCD o (rowN K 3) A,
    rowCD o (rowN K 4) A⟩

@[expose] noncomputable def rowKCD (o : Ops α) (K : Nat) (r : R5 α) : R5 α :=
  ⟨sel o (colN K 0) r.e0 r.e1 r.e2 r.e3 r.e4, sel o (colN K 1) r.e0 r.e1 r.e2 r.e3 r.e4,
    sel o (colN K 2) r.e0 r.e1 r.e2 r.e3 r.e4, sel o (colN K 3) r.e0 r.e1 r.e2 r.e3 r.e4,
    sel o (colN K 4) r.e0 r.e1 r.e2 r.e3 r.e4⟩

@[expose] noncomputable def mulKCD (o : Ops α) (K : Nat) (A : M5 α) : M5 α :=
  ⟨rowKCD o K A.r0, rowKCD o K A.r1, rowKCD o K A.r2, rowKCD o K A.r3, rowKCD o K A.r4⟩

@[expose] noncomputable def nconjD (o : Ops α) (A : M5 α) (K K' : Nat) : α :=
  neM o (mulCD o A K) (mulKCD o K' A)

@[expose] noncomputable def nsD (o : Ops α) (A : M5 α) (n : Nat) : α :=
  Nat.rec (motive := fun _ => α) o.t (fun n acc => o.a acc (nzv o (Nat.succ n) A)) n

@[expose] noncomputable def sqD (o : Ops α) (A : M5 α) : M5 α := mulD o A A

@[expose] noncomputable def chk1D (o : Ops α) (A : M5 α) : α :=
  o.o (o.o (o.o (bnot o (nsD o A 31)) (nconjD o A uvC uvC)) (nconjD o A tC tC))
    (bnot o (neMN o (sqD o (sqD o (sqD o (sqD o (sqD o (sqD o A)))))) idC))

@[expose] noncomputable def inDD (o : Ops α) (A : M5 α) (d : Nat) : α :=
  bnot o (o.a (o.a (o.a (nconjD o A d 16916514) (nconjD o A d 17043521))
    (o.a (nconjD o A d 18000930) (nconjD o A d 18191425)))
    (o.a (o.a (nconjD o A d 19114018) (nconjD o A d 19209281))
      (o.a (nconjD o A d 20128802) (nconjD o A d 20224065))))

@[expose] noncomputable def inVD (o : Ops α) (A : M5 α) (d : Nat) : α :=
  bnot o (o.a (o.a (nconjD o A d 17043521) (nconjD o A d 20224065))
    (o.a (nconjD o A d 18191425) (nconjD o A d 19209281)))

@[expose] noncomputable def chk2D (o : Ops α) (A : M5 α) : α :=
  o.o (o.o (o.o (bnot o (nsD o A 31)) (nconjD o A uvC uvC))
    (bnot o (o.a (inDD o A uvC) (o.a (inDD o A tC) (inDD o A uC)))))
    (o.a (inVD o A uvC) (inVD o A tC))

section bind

variable (o : Ops α) (hbd : ∀ y k, o.bd y k = k y)
include hbd

theorem rowK_eq (s : R5 α) (A : M5 α) (k : R5 α → α) : rowK o s A k = k (rowD o s A) := by
  simp only [rowK, hbd, rowD]

theorem mulK_eq (A B : M5 α) (k : M5 α → α) : mulK o A B k = k (mulD o A B) := by
  simp only [mulK, rowK_eq o hbd, mulD]

theorem rowCK_eq (s : Nat) (A : M5 α) (k : R5 α → α) : rowCK o s A k = k (rowCD o s A) := by
  simp only [rowCK, hbd, rowCD]

theorem rowKC_eq (K : Nat) (r : R5 α) (k : R5 α → α) : rowKC o K r k = k (rowKCD o K r) := by
  simp only [rowKC, hbd, rowKCD]

theorem nconj_eq (A : M5 α) (K K' : Nat) : nconj o A K K' = nconjD o A K K' := by
  simp only [nconj, mulCK, mulKC, rowCK_eq o hbd, rowKC_eq o hbd, nconjD, mulCD, mulKCD]

theorem nsK_eq (A : M5 α) : nsK o A = nsD o A 31 := by
  simp only [nsK, hbd, nsD]

theorem chk1_eq (A : M5 α) : chk1 o A = chk1D o A := by
  simp only [chk1, hbd, nsK_eq o hbd, nconj_eq o hbd, mulK_eq o hbd, chk1D, sqD]

theorem chk2_eq (A : M5 α) : chk2 o A = chk2D o A := by
  simp only [chk2, inD, inV, hbd, nsK_eq o hbd, nconj_eq o hbd, chk2D, inDD, inVD]

end bind

section map

variable (o : Ops α) (o' : Ops β) (f : α → β) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q))
  (ho : ∀ p q, f (o.o p q) = o'.o (f p) (f q)) (hx : ∀ p q, f (o.x p q) = o'.x (f p) (f q))
  (ht : f o.t = o'.t) (hz : f o.z = o'.z)
include ha ho hx ht hz

theorem sx_map (b : Bool) (acc v : α) : f (sx o b acc v) = sx o' b (f acc) (f v) := by
  cases b <;> simp only [sx, hx]

theorem sel_map (s : Nat) (v0 v1 v2 v3 v4 : α) :
    f (sel o s v0 v1 v2 v3 v4) = sel o' s (f v0) (f v1) (f v2) (f v3) (f v4) := by
  simp only [sel, sx_map o o' f ha ho hx ht hz, hz]

theorem mulD_map (A B : M5 α) : (mulD o A B).map f = mulD o' (A.map f) (B.map f) := by
  simp only [mulD, rowD, dot, M5.map, R5.map, ha, hx]

theorem sqD_map (A : M5 α) : (sqD o A).map f = sqD o' (A.map f) :=
  mulD_map o o' f ha ho hx ht hz A A

theorem nconjD_map (A : M5 α) (K K' : Nat) :
    f (nconjD o A K K') = nconjD o' (A.map f) K K' := by
  simp only [nconjD, neM, neR, mulCD, mulKCD, rowCD, rowKCD, M5.map, R5.map, ho, hx,
    sel_map o o' f ha ho hx ht hz]

theorem bnot_map (p : α) : f (bnot o p) = bnot o' (f p) := by
  simp only [bnot, hx, ht]

theorem neB_map (p : α) (b : Bool) : f (neB o p b) = neB o' (f p) b := by
  cases b <;> simp only [neB, hx, ht]

theorem neMN_map (A : M5 α) (K : Nat) : f (neMN o A K) = neMN o' (A.map f) K := by
  simp only [neMN, neRN, M5.map, R5.map, ho, neB_map o o' f ha ho hx ht hz]

theorem nsD_map (A : M5 α) : ∀ n, f (nsD o A n) = nsD o' (A.map f) n
  | 0 => ht
  | n + 1 => by
    change f (o.a (nsD o A n) (nzv o (n + 1) A)) =
      o'.a (nsD o' (A.map f) n) (nzv o' (n + 1) (A.map f))
    rw [ha, nsD_map A n]
    simp only [nzv, M5.map, R5.map, ho, sel_map o o' f ha ho hx ht hz]

theorem chk1D_map (A : M5 α) : f (chk1D o A) = chk1D o' (A.map f) := by
  simp only [chk1D, ho, bnot_map o o' f ha ho hx ht hz, nsD_map o o' f ha ho hx ht hz,
    nconjD_map o o' f ha ho hx ht hz, neMN_map o o' f ha ho hx ht hz,
    sqD_map o o' f ha ho hx ht hz]

theorem chk2D_map (A : M5 α) : f (chk2D o A) = chk2D o' (A.map f) := by
  simp only [chk2D, inDD, inVD, ho, ha, bnot_map o o' f ha ho hx ht hz,
    nsD_map o o' f ha ho hx ht hz, nconjD_map o o' f ha ho hx ht hz]

end map

@[expose] def boolOps : Ops Bool := ⟨and, or, xor, true, false, fun y k => k y⟩

@[expose] def rowB (r : Nat) : R5 Bool :=
  ⟨r.testBit 0, r.testBit 1, r.testBit 2, r.testBit 3, r.testBit 4⟩

@[expose] def ofC (c : Nat) : M5 Bool :=
  ⟨rowB (r0 c), rowB (r1 c), rowB (r2 c), rowB (r3 c), rowB (r4 c)⟩

theorem sx_bool (b acc v : Bool) : sx boolOps b acc v = xor acc (b && v) := by
  cases b <;> simp [sx, boolOps]

theorem sel_bool (s : Nat) (v0 v1 v2 v3 v4 : Bool) : sel boolOps s v0 v1 v2 v3 v4 =
    xor (xor (xor (xor (s.testBit 0 && v0) (s.testBit 1 && v1)) (s.testBit 2 && v2))
      (s.testBit 3 && v3)) (s.testBit 4 && v4) := by
  simp only [sel, sx_bool, ← testBit_eq_bitB]
  simp [boolOps]

theorem rowN_eq (K i : Nat) : rowN K i = K / 2 ^ (5 * i) % 32 := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := rfl
  change (K >>> (5 * i)) &&& 31 = _
  rw [Nat.shiftRight_eq_div_pow, h31, Nat.and_two_pow_sub_one_eq_mod]

theorem rowN_0 (K : Nat) : rowN K 0 = r0 K := by rw [rowN_eq]; simp [r0]
theorem rowN_1 (K : Nat) : rowN K 1 = r1 K := by rw [rowN_eq]; simp [r1]
theorem rowN_2 (K : Nat) : rowN K 2 = r2 K := by rw [rowN_eq]; simp [r2]
theorem rowN_3 (K : Nat) : rowN K 3 = r3 K := by rw [rowN_eq]; simp [r3]
theorem rowN_4 (K : Nat) : rowN K 4 = r4 K := by rw [rowN_eq]; simp [r4]

theorem r0_bit (c : Nat) {m : Nat} (hm : m < 5) : (r0 c).testBit m = c.testBit m := by
  have h : (32 : Nat) = 2 ^ 5 := rfl
  rw [r0, h, Nat.testBit_mod_two_pow]
  simp [hm]

theorem rk_bit (c k : Nat) {m : Nat} (hm : m < 5) :
    (c / 2 ^ (5 * k) % 32).testBit m = c.testBit (5 * k + m) := by
  have h : (32 : Nat) = 2 ^ 5 := rfl
  rw [h, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hm, Nat.add_comm]

theorem r1_bit (c : Nat) {m : Nat} (hm : m < 5) : (r1 c).testBit m = c.testBit (5 + m) :=
  rk_bit c 1 hm
theorem r2_bit (c : Nat) {m : Nat} (hm : m < 5) : (r2 c).testBit m = c.testBit (10 + m) :=
  rk_bit c 2 hm
theorem r3_bit (c : Nat) {m : Nat} (hm : m < 5) : (r3 c).testBit m = c.testBit (15 + m) :=
  rk_bit c 3 hm
theorem r4_bit (c : Nat) {m : Nat} (hm : m < 5) : (r4 c).testBit m = c.testBit (20 + m) :=
  rk_bit c 4 hm

theorem tb_lor (a b j : Nat) : (Nat.lor a b).testBit j = (a.testBit j || b.testBit j) :=
  Nat.testBit_or a b j

theorem tb_land1 (x j : Nat) : (Nat.land x 1).testBit j = (decide (j < 1) && x.testBit j) := by
  have h : Nat.land x 1 = x % 2 ^ 1 := Nat.and_one_is_mod x
  rw [h, Nat.testBit_mod_two_pow]

theorem tb_shl (x n j : Nat) :
    (Nat.shiftLeft x n).testBit j = (decide (j ≥ n) && x.testBit (j - n)) :=
  Nat.testBit_shiftLeft x

theorem tb_shr (x n j : Nat) : (Nat.shiftRight x n).testBit j = x.testBit (n + j) :=
  Nat.testBit_shiftRight x

theorem colN_bit (K : Nat) {m : Nat} (hm : m < 5) : (colN K m).testBit 0 = (r0 K).testBit m ∧
    (colN K m).testBit 1 = (r1 K).testBit m ∧ (colN K m).testBit 2 = (r2 K).testBit m ∧
    (colN K m).testBit 3 = (r3 K).testBit m ∧ (colN K m).testBit 4 = (r4 K).testBit m := by
  rw [r0_bit K hm, r1_bit K hm, r2_bit K hm, r3_bit K hm, r4_bit K hm]
  simp only [colN, tb_lor, tb_land1, tb_shl, tb_shr]
  simp [Nat.add_comm]

theorem mulD_ofC (a b : Nat) : mulD boolOps (ofC a) (ofC b) = ofC (mulC a b) := by
  simp only [mulD, rowD, dot, ofC, rowB, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC, vm,
    vm5_testBit]
  rfl

theorem mulCD_ofC (a K : Nat) : mulCD boolOps (ofC a) K = ofC (mulC a K) := by
  simp only [mulCD, rowCD, sel_bool, ofC, rowB, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC, vm,
    vm5_testBit, rowN_0, rowN_1, rowN_2, rowN_3, rowN_4]

theorem mulKCD_ofC (K a : Nat) : mulKCD boolOps K (ofC a) = ofC (mulC K a) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := colN_bit K (m := 0) (by omega)
  obtain ⟨b0, b1, b2, b3, b4⟩ := colN_bit K (m := 1) (by omega)
  obtain ⟨c0, c1, c2, c3, c4⟩ := colN_bit K (m := 2) (by omega)
  obtain ⟨d0, d1, d2, d3, d4⟩ := colN_bit K (m := 3) (by omega)
  obtain ⟨e0, e1, e2, e3, e4⟩ := colN_bit K (m := 4) (by omega)
  simp only [mulKCD, rowKCD, sel_bool, ofC, rowB, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC,
    vm, vm5_testBit, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, d0, d1, d2, d3,
    d4, e0, e1, e2, e3, e4, Bool.and_comm]

theorem sqD_ofC (a : Nat) : sqD boolOps (ofC a) = ofC (sqC a) := mulD_ofC a a

theorem eq_of_bits {a b : Nat} (ha : a < N) (hb : b < N)
    (h : ∀ j, j < 25 → a.testBit j = b.testBit j) : a = b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 25
  · exact h j hj
  · have h25 : 2 ^ 25 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    unfold N at ha hb
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem neM_ofC {a b : Nat} (ha : a < N) (hb : b < N) :
    neM boolOps (ofC a) (ofC b) = !(decide (a = b)) := by
  by_cases h : a = b
  · subst h
    simp [neM, neR, boolOps]
  · simp only [h, decide_false, Bool.not_false]
    by_contra hne
    apply h
    refine eq_of_bits ha hb fun j hj => ?_
    have xf : ∀ p q : Bool, (p ^^ q) = false → p = q := by decide
    simp (disch := omega) only [neM, neR, ofC, rowB, boolOps, Bool.or_eq_true, not_or,
      Bool.not_eq_true, r0_bit, r1_bit, r2_bit, r3_bit, r4_bit] at hne
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, ⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩⟩,
      ⟨⟨⟨⟨h10, h11⟩, h12⟩, h13⟩, h14⟩⟩, ⟨⟨⟨⟨h15, h16⟩, h17⟩, h18⟩, h19⟩⟩,
      ⟨⟨⟨⟨h20, h21⟩, h22⟩, h23⟩, h24⟩⟩ := hne
    interval_cases j <;> exact xf _ _ (by assumption)

theorem neMN_ofC {a K : Nat} (ha : a < N) (hK : K < N) :
    neMN boolOps (ofC a) K = !(decide (a = K)) := by
  rw [← neM_ofC ha hK]
  have hB : ∀ p b, neB boolOps p b = boolOps.x p b := by
    intro p b
    cases b <;> cases p <;> rfl
  simp only [neMN, neRN, hB, ← testBit_eq_bitB, rowN_0, rowN_1, rowN_2, rowN_3, rowN_4, neM,
    neR, ofC, rowB]

theorem or5_eq {x : Nat} (hx : x < 32) : (x.testBit 0 || x.testBit 1 || x.testBit 2 ||
    x.testBit 3 || x.testBit 4) = decide (x ≠ 0) := by
  interval_cases x <;> rfl

theorem nzv_ofC (v c : Nat) : nzv boolOps v (ofC c) = decide (vm v c ≠ 0) := by
  rw [← or5_eq (vm_lt v c)]
  simp only [nzv, sel_bool, ofC, rowB, vm, vm5_testBit]
  rfl

theorem nsD_ofC (c : Nat) :
    ∀ n, nsD boolOps (ofC c) n = true ↔ ∀ v, 0 < v → v ≤ n → vm v c ≠ 0
  | 0 => by
    simp only [nsD, boolOps]
    exact ⟨fun _ v h0 h1 => absurd h1 (by omega), fun _ => rfl⟩
  | n + 1 => by
    change (nsD boolOps (ofC c) n && nzv boolOps (n + 1) (ofC c)) = true ↔ _
    rw [Bool.and_eq_true, nsD_ofC c n, nzv_ofC, decide_eq_true_iff]
    constructor
    · rintro ⟨h, h'⟩ v h0 h1
      rcases Nat.lt_or_ge v (n + 1) with hv | hv
      · exact h v h0 (by omega)
      · obtain rfl : v = n + 1 := by omega
        exact h'
    · intro h
      exact ⟨fun v h0 h1 => h v h0 (by omega), h (n + 1) (by omega) le_rfl⟩

theorem nsD_31 {c : Nat} (hns : nonsing c = true) : nsD boolOps (ofC c) 31 = true := by
  rw [nsD_ofC]
  intro v h0 h1
  exact (nonsing_iff c).1 hns v h0 (by omega)

theorem nconjD_ofC (c K K' : Nat) :
    nconjD boolOps (ofC c) K K' = !(decide (mulC c K = mulC K' c)) := by
  rw [nconjD, mulCD_ofC, mulKCD_ofC, neM_ofC (mulC_lt _ _) (mulC_lt _ _)]

theorem idC_lt : idC < N := by decide

theorem chk1D_ofC {c : Nat} (hc : c < N) (h : chk1D boolOps (ofC c) = true)
    (hns : nonsing c = true) (huv : mulC c uvC = mulC uvC c) (ht : mulC c tC = mulC tC c) :
    powC c 64 = idC := by
  have hsq : ∀ x, sqC x < N := fun x => mulC_lt x x
  rw [chk1D, nsD_31 hns, nconjD_ofC, nconjD_ofC, huv, ht, sqD_ofC, sqD_ofC, sqD_ofC, sqD_ofC,
    sqD_ofC, sqD_ofC, neMN_ofC (hsq _) idC_lt] at h
  rw [powC_64 hc]
  simpa [boolOps, bnot] using h

theorem beq_dec (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem inDD_ofC (c d : Nat) :
    inDD boolOps (ofC c) d = dCodes.any fun d' => mulC c d == mulC d' c := by
  simp only [inDD, nconjD_ofC]
  simp only [dCodes, bnot, boolOps, List.any_cons, List.any_nil, beq_dec, Bool.not_and,
    Bool.not_not, Bool.xor_true, Bool.or_false, Bool.or_assoc]

theorem inVD_ofC (c d : Nat) :
    inVD boolOps (ofC c) d = vCodes.any fun d' => mulC c d == mulC d' c := by
  simp only [inVD, nconjD_ofC]
  simp only [vCodes, idC, uvC, tC, bnot, boolOps, List.any_cons, List.any_nil, beq_dec,
    Bool.not_and, Bool.not_not, Bool.xor_true, Bool.or_false, Bool.or_assoc]

theorem chk2D_ofC {c : Nat} (h : chk2D boolOps (ofC c) = true) (hns : nonsing c = true)
    (huv : mulC c uvC = mulC uvC c) (hD : normD c = true) : normV c = true := by
  rw [chk2D, nsD_31 hns, nconjD_ofC, huv, inDD_ofC, inDD_ofC, inDD_ofC, inVD_ofC,
    inVD_ofC] at h
  simp only [normD, List.all, Bool.and_true] at hD
  simp only [normV, List.all, Bool.and_true]
  simp only [boolOps] at h
  rw [hD] at h
  simpa [boolOps, bnot] using h

theorem rec_all (g : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun s acc => Bool.rec (motive := fun _ => Bool) false (g s) acc) n = true →
    ∀ s, s < n → g s = true
  | 0, _, s, hs => absurd hs (by omega)
  | n + 1, h, s, hs => by
    change Bool.rec (motive := fun _ => Bool) false (g n)
      (Nat.rec (motive := fun _ => Bool) true
        (fun s acc => Bool.rec (motive := fun _ => Bool) false (g s) acc) n) = true at h
    cases hr : Nat.rec (motive := fun _ => Bool) true
        (fun s acc => Bool.rec (motive := fun _ => Bool) false (g s) acc) n with
    | false =>
      rw [hr] at h
      exact absurd h Bool.false_ne_true
    | true =>
      rw [hr] at h
      rcases Nat.lt_or_ge s n with h' | h'
      · exact rec_all g n hr s h'
      · obtain rfl : s = n := by omega
        exact h

theorem tT_bit (m : Nat) {i : Nat} (hi : i < 2 ^ m) :
    (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1).testBit i = true := by
  rw [Nat.sub_eq, Nat.pow_eq, Nat.pow_eq, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  exact hi

section Cover

open CFSG.KC.F4M3B (frcN_eq frc_eq pln_bit)

theorem nthL_eq (L : List Nat) (i : Nat) : nthL L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n

theorem allL_mem {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ e ∈ L, f e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | a :: l, h, e, he => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allL f l) (f a) = true := h
    cases hfa : f a <;> rw [hfa] at h'
    · exact absurd h' Bool.false_ne_true
    · rcases List.mem_cons.mp he with rfl | he
      · exact hfa
      · exact allL_mem h' e he

theorem natRec_succ {α : Type} (z : α) (s : Nat → α → α) (n : Nat) :
    (Nat.rec (motive := fun _ => α) z s (n + 1) : α) = s n (Nat.rec (motive := fun _ => α) z s n) :=
  rfl

theorem cv_lor (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem cv_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem cv_xor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem cv_shl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem cv_shr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl

theorem natOps_bd (t y : Nat) (k : Nat → Nat) : (natOps t).bd y k = k y := frcN_eq y k

theorem cv_flip_bit (c j i : Nat) : (c ^^^ 2 ^ j).testBit i = (c.testBit i ^^ decide (j = i)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem cv_flip_add {c j : Nat} (h : c.testBit j = false) : 2 ^ j + c = c ^^^ 2 ^ j := by
  have hx : c ^^^ 2 ^ j = c ||| 2 ^ j := Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hi : j = i
    · subst hi
      simp [h]
    · simp [hi]
  have hr : c % 2 ^ (j + 1) < 2 ^ j := by
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [Nat.testBit_mod_two_pow]
    by_cases hij : i = j
    · subst hij
      simp [h]
    · have : ¬ i < j + 1 := by omega
      simp [this]
  have hc : c = 2 ^ (j + 1) * (c / 2 ^ (j + 1)) + c % 2 ^ (j + 1) := (Nat.div_add_mod _ _).symm
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
  have h1 : 2 ^ j + c = 2 ^ (j + 1) * (c / 2 ^ (j + 1)) + (c % 2 ^ (j + 1) + 2 ^ j) := by omega
  have h2 : c % 2 ^ (j + 1) + 2 ^ j < 2 ^ (j + 1) := by omega
  have h3 : c % 2 ^ (j + 1) < 2 ^ (j + 1) := by omega
  rw [hx, h1, Nat.two_pow_add_eq_or_of_lt h2, ← Nat.or_two_pow_eq_add_of_lt hr, ← Nat.or_assoc,
    ← Nat.two_pow_add_eq_or_of_lt h3, ← hc]

theorem cv_shr_and_one (c k : Nat) : (c >>> k) &&& 1 = if c.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ k) with h | h <;> simp [h]

theorem tauN_eq (c op : Nat) :
    tauN c op = c ^^^ (if c.testBit (Nat.shiftRight op 5) then 2 ^ Nat.land op 31 else 0) := by
  change c ^^^ (((c >>> Nat.shiftRight op 5) &&& 1) <<< Nat.land op 31) = _
  rw [cv_shr_and_one]
  split <;> simp [Nat.one_shiftLeft]

theorem tauN_bit (c op i : Nat) : (tauN c op).testBit i =
    (c.testBit i ^^ (c.testBit (Nat.shiftRight op 5) && decide (Nat.land op 31 = i))) := by
  rw [tauN_eq]
  split <;> simp_all [Nat.testBit_two_pow]

theorem opOK_spec {op : Nat} (h : opOK op = true) :
    Nat.land op 31 < 21 ∧ Nat.shiftRight op 5 < 21 ∧ Nat.land op 31 ≠ Nat.shiftRight op 5 := by
  simp only [opOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  refine ⟨h.1.1, h.1.2, fun he => ?_⟩
  have h2 := h.2
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem tauN_lt {op : Nat} (hop : opOK op = true) {c : Nat} (hc : c < 2 ^ 21) :
    tauN c op < 2 ^ 21 := by
  rw [tauN_eq]
  split
  · exact Nat.xor_lt_two_pow hc (Nat.pow_lt_pow_right (by omega) (opOK_spec hop).1)
  · rw [Nat.xor_zero]
    exact hc

theorem ptS_lt : ∀ {ops : List Nat}, (∀ op ∈ ops, opOK op = true) → ∀ {c : Nat}, c < 2 ^ 21 →
    ptS ops c < 2 ^ 21
  | [], _, _, hc => hc
  | op :: ops, hops, _, hc =>
    tauN_lt (hops op (List.mem_cons.mpr (Or.inl rfl)))
      (ptS_lt (fun o ho => hops o (List.mem_cons_of_mem _ ho)) hc)

theorem tv_core {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
    {j k : Nat} (hj : j < 21) (hk : k < 21) (hjk : j ≠ k) (I : Nat) {c : Nat} (hc : c < 2 ^ 21) :
    (Nat.lor (Nat.xor I (Nat.land I (nthL Ms k)))
      (Nat.lor (Nat.shiftRight (Nat.land (Nat.land I (nthL Ms k)) (nthL Ms j)) (Nat.shiftLeft 1 j))
        (Nat.shiftLeft (Nat.xor (Nat.land I (nthL Ms k)) (Nat.land (Nat.land I (nthL Ms k))
          (nthL Ms j))) (Nat.shiftLeft 1 j)))).testBit c =
    I.testBit (c ^^^ (if c.testBit k then 2 ^ j else 0)) := by
  simp only [cv_lor, cv_land, cv_xor, cv_shl, cv_shr, Nat.one_shiftLeft, Nat.testBit_or,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hMs k hk,
    hMs j hj]
  have hpj : 2 ^ j < 2 ^ 21 := Nat.pow_lt_pow_right (by omega) hj
  have hcd : decide (c < 2 ^ 21) = true := decide_eq_true hc
  have hf : c ^^^ 2 ^ j < 2 ^ 21 := Nat.xor_lt_two_pow hc hpj
  have hfk : (c ^^^ 2 ^ j).testBit k = c.testBit k := by
    rw [cv_flip_bit]
    simp [hjk]
  cases hcj : c.testBit j
  · rw [cv_flip_add hcj]
    have hfj : (c ^^^ 2 ^ j).testBit j = true := by
      rw [cv_flip_bit, hcj]
      simp
    have hlow : (decide (c ≥ 2 ^ j) && ((I.testBit (c - 2 ^ j) &&
        (decide (c - 2 ^ j < 2 ^ 21) && (c - 2 ^ j).testBit k)) ^^
        (I.testBit (c - 2 ^ j) && (decide (c - 2 ^ j < 2 ^ 21) && (c - 2 ^ j).testBit k) &&
          (decide (c - 2 ^ j < 2 ^ 21) && (c - 2 ^ j).testBit j)))) = false := by
      by_cases hge : c ≥ 2 ^ j
      · have hdj : (c - 2 ^ j).testBit j = true := by
          cases hdj : (c - 2 ^ j).testBit j
          · have e := cv_flip_add hdj
            rw [Nat.add_sub_cancel' hge] at e
            rw [e, cv_flip_bit, hdj] at hcj
            simp at hcj
          · rfl
        have hdl : decide (c - 2 ^ j < 2 ^ 21) = true :=
          decide_eq_true (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hc)
        rw [hdj, hdl]
        cases I.testBit (c - 2 ^ j) <;> cases (c - 2 ^ j).testBit k <;> simp
      · simp [hge]
    rw [hlow, decide_eq_true hf, hfj, hfk, hcd]
    cases hck : c.testBit k <;> simp
  · have e0 : (c ^^^ 2 ^ j).testBit j = false := by
      rw [cv_flip_bit, hcj]
      simp
    have e1 := cv_flip_add e0
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e1
    have hsub : c - 2 ^ j = c ^^^ 2 ^ j := by omega
    have hge : c ≥ 2 ^ j := by omega
    have hA : (2 ^ j + c).testBit j = false := by
      rw [Nat.testBit_two_pow_add_eq, hcj]
      rfl
    rw [hsub, hA, decide_eq_true hf, decide_eq_true hge, hfk, hcd, e0]
    cases hck : c.testBit k <;> simp

theorem tvI_bit {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
    {op : Nat} (hop : opOK op = true) (I : Nat) {c : Nat} (hc : c < 2 ^ 21) :
    (tvI Ms I op).testBit c = I.testBit (tauN c op) := by
  obtain ⟨hj, hk, hjk⟩ := opOK_spec hop
  rw [tauN_eq, ← tv_core hMs hj hk hjk I hc]
  simp only [tvI, frcN_eq]

theorem imgS_bit {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j)) :
    ∀ {ops : List Nat}, (∀ op ∈ ops, opOK op = true) → ∀ (I : Nat) {c : Nat}, c < 2 ^ 21 →
      (imgS Ms I ops).testBit c = I.testBit (ptS ops c)
  | [], _, _, _, _ => rfl
  | op :: ops, hops, I, c, hc => by
    have hops' : ∀ o ∈ ops, opOK o = true := fun o ho => hops o (List.mem_cons_of_mem _ ho)
    have e : imgS Ms I (op :: ops) = imgS Ms (tvI Ms I op) ops :=
      frcN_eq (tvI Ms I op) (fun J => imgS Ms J ops)
    rw [e, imgS_bit hMs hops' _ hc,
      tvI_bit hMs (hops op (List.mem_cons.mpr (Or.inl rfl))) _ (ptS_lt hops' hc)]
    rfl

theorem lin_zero {F : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) : F 0 = 0 := by
  have := hF 0 0
  simp only [Nat.xor_self] at this
  exact this

theorem lin_ext {F G : Nat → Nat} {m : Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) (hb : ∀ b < m, F (2 ^ b) = G (2 ^ b)) :
    ∀ n ≤ m, ∀ c < 2 ^ n, F c = G c := by
  intro n
  induction n with
  | zero =>
    intro _ c hc
    have : c = 0 := by
      rw [Nat.pow_zero] at hc
      omega
    rw [this, lin_zero hF, lin_zero hG]
  | succ n ih =>
    intro hn c hc
    by_cases hlt : c < 2 ^ n
    · exact ih (by omega) c hlt
    · have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
      obtain ⟨d, rfl⟩ : ∃ d, c = 2 ^ n + d := ⟨c - 2 ^ n, by omega⟩
      have hd : d < 2 ^ n := by omega
      rw [cv_flip_add (Nat.testBit_lt_two_pow hd), hF, hG, ih (by omega) d hd, hb n (by omega)]

theorem ptS_xor : ∀ (ops : List Nat) (a b : Nat), ptS ops (a ^^^ b) = ptS ops a ^^^ ptS ops b
  | [], _, _ => rfl
  | op :: ops, a, b => by
    change tauN (ptS ops (a ^^^ b)) op = tauN (ptS ops a) op ^^^ tauN (ptS ops b) op
    rw [ptS_xor ops a b]
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [tauN_bit, Nat.testBit_xor]
    cases (ptS ops a).testBit i <;> cases (ptS ops b).testBit i <;>
      cases (ptS ops a).testBit (Nat.shiftRight op 5) <;>
      cases (ptS ops b).testBit (Nat.shiftRight op 5) <;> cases decide (Nat.land op 31 = i) <;> rfl

theorem r0_xor (x y : Nat) : r0 (x ^^^ y) = r0 x ^^^ r0 y := Nat.xor_mod_two_pow (n := 5)

theorem rdm_xor (x y s : Nat) :
    (x ^^^ y) / 2 ^ s % 2 ^ 5 = x / 2 ^ s % 2 ^ 5 ^^^ y / 2 ^ s % 2 ^ 5 := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem r1_xor (x y : Nat) : r1 (x ^^^ y) = r1 x ^^^ r1 y := rdm_xor x y 5
theorem r2_xor (x y : Nat) : r2 (x ^^^ y) = r2 x ^^^ r2 y := rdm_xor x y 10
theorem r3_xor (x y : Nat) : r3 (x ^^^ y) = r3 x ^^^ r3 y := rdm_xor x y 15
theorem r4_xor (x y : Nat) : r4 (x ^^^ y) = r4 x ^^^ r4 y := rdm_xor x y 20

theorem ite_xor_m (b : Bool) (x y : Nat) : (if b = true then x ^^^ y else 0) =
    (if b = true then x else 0) ^^^ (if b = true then y else 0) := by
  cases b <;> simp

theorem ite_xor_v (p q : Bool) (m : Nat) : (if (p ^^ q) = true then m else 0) =
    (if p = true then m else 0) ^^^ (if q = true then m else 0) := by
  cases p <;> cases q <;> simp

theorem vm5_xor_m (v a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Nat) :
    vm5 v (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) (a4 ^^^ b4) =
      vm5 v a0 a1 a2 a3 a4 ^^^ vm5 v b0 b1 b2 b3 b4 := by
  unfold vm5
  rw [ite_xor_m, ite_xor_m, ite_xor_m, ite_xor_m, ite_xor_m]
  ac_rfl

theorem vm5_xor_v (v w m0 m1 m2 m3 m4 : Nat) :
    vm5 (v ^^^ w) m0 m1 m2 m3 m4 = vm5 v m0 m1 m2 m3 m4 ^^^ vm5 w m0 m1 m2 m3 m4 := by
  unfold vm5
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
    ite_xor_v, ite_xor_v, ite_xor_v, ite_xor_v, ite_xor_v]
  ac_rfl

theorem mulC_lt' (a b : Nat) : mulC a b < 2 ^ 25 := mulC_lt a b

theorem mulC_xor_l (a b g : Nat) : mulC (a ^^^ b) g = mulC a g ^^^ mulC b g := by
  refine code_ext (mulC_lt _ _) (Nat.xor_lt_two_pow (mulC_lt' a g) (mulC_lt' b g)) ?_ ?_ ?_ ?_ ?_ <;>
  simp only [r0_xor, r1_xor, r2_xor, r3_xor, r4_xor, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC,
    vm, vm5_xor_m]

theorem mulC_xor_r (g a b : Nat) : mulC g (a ^^^ b) = mulC g a ^^^ mulC g b := by
  refine code_ext (mulC_lt _ _) (Nat.xor_lt_two_pow (mulC_lt' g a) (mulC_lt' g b)) ?_ ?_ ?_ ?_ ?_ <;>
  simp only [r0_xor, r1_xor, r2_xor, r3_xor, r4_xor, r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC,
    vm, vm5_xor_v]

def CovInv (P : Nat → Prop) (U : Nat) : Prop := ∀ p < 2 ^ 21, U.testBit p = true → P p

def GoodOs (P : Nat → Prop) (Os : List (List Nat)) : Prop :=
  ∀ ops ∈ Os, (∀ op ∈ ops, opOK op = true) ∧ ∀ p < 2 ^ 21, P (ptS ops p) → P p

theorem roundS_inv {P : Nat → Prop} {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
    {U : Nat} (hU : CovInv P U) : ∀ {Os : List (List Nat)}, GoodOs P Os → CovInv P (roundS Ms Os U)
  | [], _ => hU
  | ops :: Os, hOs => by
    intro c hc h
    have e : roundS Ms (ops :: Os) U = roundS Ms Os U ||| imgS Ms U ops :=
      frcN_eq (roundS Ms Os U) (fun acc => Nat.lor acc (imgS Ms U ops))
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact roundS_inv hMs hU (fun o ho => hOs o (List.mem_cons_of_mem _ ho)) c hc h
    · obtain ⟨hops, hw⟩ := hOs ops (List.mem_cons.mpr (Or.inl rfl))
      rw [imgS_bit hMs hops U hc] at h
      exact hw c hc (hU _ (ptS_lt hops hc) h)

theorem roundsS_inv {P : Nat → Prop} {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
    {Os : List (List Nat)} (hOs : GoodOs P Os) :
    ∀ (n : Nat) {U : Nat}, CovInv P U → CovInv P (roundsS Ms Os n U)
  | 0, _, hU => hU
  | n + 1, U, hU => by
    have e : roundsS Ms Os (n + 1) U = roundS Ms Os (roundsS Ms Os n U) :=
      frcN_eq (roundsS Ms Os n U) (fun V => roundS Ms Os V)
    rw [e]
    exact roundS_inv hMs (roundsS_inv hMs hOs n hU) hOs

theorem leafS_bit : ∀ {s : List Nat} {c : Nat}, (leafS s).testBit c = true →
    ∃ d ∈ s, Nat.land d 1023 = c
  | [], c, h => by
    change Nat.testBit 0 c = true at h
    simp at h
  | d :: s, c, h => by
    change (Nat.lor (leafS s) (Nat.shiftLeft 1 (Nat.land d 1023))).testBit c = true at h
    rw [cv_lor, cv_shl, Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨d', hd', h'⟩ := leafS_bit h
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩
    · exact ⟨d, List.mem_cons.mpr (Or.inl rfl), h⟩

theorem leafS_lt (s : List Nat) {m : Nat} (hm : 1024 ≤ m) : leafS s < 2 ^ m :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases h : (leafS s).testBit i
    · rfl
    · obtain ⟨d, -, hd⟩ := leafS_bit h
      rw [cv_land] at hd
      have := @Nat.and_le_right d 1023
      omega

theorem indS_bit {X : List Nat} {B : List (List Nat)} {l : Nat} :
    ∀ {S : List (List Nat)} {j0 : Nat}, seedsOK X B l S j0 = true → ∀ {c : Nat},
    (indS S).testBit c = true → ∃ j d, seedOK X B l (j0 + j) d = true ∧ c = 1024 * j + Nat.land d 1023
  | [], _, _, c, h => by
    change Nat.testBit 0 c = true at h
    simp at h
  | s :: S, j0, hb, c, h => by
    have hb' : Bool.rec (motive := fun _ => Bool) false (seedsOK X B l S (j0 + 1))
        (allL (seedOK X B l j0) s) = true := hb
    cases hl : allL (seedOK X B l j0) s <;> rw [hl] at hb'
    · exact absurd hb' Bool.false_ne_true
    have ei : indS (s :: S) = Nat.lor (Nat.shiftLeft (indS S) 1024) (leafS s) :=
      frcN_eq (indS S) (fun acc => Nat.lor (Nat.shiftLeft acc 1024) (leafS s))
    rw [ei, cv_lor, cv_shl, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with ⟨hc, h⟩ | h
    · obtain ⟨j, d, hd, h'⟩ := indS_bit hb' h
      have e : j0 + (j + 1) = j0 + 1 + j := by omega
      exact ⟨j + 1, d, by rw [e]; exact hd, by omega⟩
    · obtain ⟨d, hd, h'⟩ := leafS_bit h
      exact ⟨0, d, allL_mem hl d hd, by omega⟩

theorem msW_spec {k : List Nat → Bool} (h : msW k = true) :
    ∃ Ms : List Nat, (∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
      ∧ k Ms = true := by
  simp only [msW, frc_eq] at h
  refine ⟨_, fun j hj x => ?_, h⟩
  rw [← pln_bit j 21 x, nthL_eq]
  interval_cases j <;> simp only [List.getD_cons_succ, List.getD_cons_zero]

theorem rb0_bit (c e : Nat) : (r0 c).testBit e = (decide (e < 5) && c.testBit e) :=
  Nat.testBit_mod_two_pow c 5 e

theorem rdm_bit (c s e : Nat) :
    (c / 2 ^ s % 2 ^ 5).testBit e = (decide (e < 5) && c.testBit (e + s)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem rb1_bit (c e : Nat) : (r1 c).testBit e = (decide (e < 5) && c.testBit (e + 5)) :=
  rdm_bit c 5 e
theorem rb2_bit (c e : Nat) : (r2 c).testBit e = (decide (e < 5) && c.testBit (e + 10)) :=
  rdm_bit c 10 e
theorem rb3_bit (c e : Nat) : (r3 c).testBit e = (decide (e < 5) && c.testBit (e + 15)) :=
  rdm_bit c 15 e
theorem lt16 {x : Nat} (hx : x < 32) : decide (x < 16) = !x.testBit 4 := by
  interval_cases x <;> decide

theorem stabW4_eq (c : Nat) :
    stabW4 c = !(c.testBit 4 || c.testBit 9 || c.testBit 14 || c.testBit 19) := by
  simp only [stabW4, lt16 (r0_lt c), lt16 (r1_lt c), lt16 (r2_lt c), lt16 (r3_lt c), rb0_bit,
    rb1_bit, rb2_bit, rb3_bit, decide_true, Bool.true_and]
  cases c.testBit 4 <;> cases c.testBit 9 <;> cases c.testBit 14 <;> cases c.testBit 19 <;> rfl

theorem allOnes_bit {X c : Nat} (hc : c < X) : (Nat.sub (Nat.shiftLeft 1 X) 1).testBit c = true := by
  have e : Nat.sub (Nat.shiftLeft 1 X) 1 = 2 ^ X - 1 := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hc

end Cover

theorem mUT_bit (q : Nat) : (1082401 : Nat).testBit q = decide (q < 25 ∧ q % 5 = 0) := by
  by_cases hq : q < 25
  · interval_cases q <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1082401 < 2 ^ 25)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hq]

theorem rUT_bit : ∀ r < 32, ∀ p < 25, (r * 1082401).testBit p = r.testBit (p % 5) := by decide

theorem rUT_lt : ∀ r < 32, r * 1082401 < 2 ^ 25 := by decide

theorem mtUT_lt {r : Nat} (hr : r < 32) (b j : Nat) : mtUT r b j < 2 ^ 25 :=
  Nat.and_lt_two_pow _ (rUT_lt r hr)

theorem mulUT_lt (a b : Nat) : mulUT a b < N := by
  have h := fun i (h : i < 32) j => mtUT_lt h b j
  unfold mulUT N
  simp only [cv_xor]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (h _ (r0_lt a) 0) (h _ (r1_lt a) 1)) (h _ (r2_lt a) 2)) (h _ (r3_lt a) 3)) (h _ (r4_lt a) 4)

@[expose] def spUT (y : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor y (Nat.shiftLeft y 1)) (Nat.shiftLeft y 2)) (Nat.shiftLeft y 3))
    (Nat.shiftLeft y 4)

@[expose] def sprUT (c : Nat) : Nat :=
  (c &&& 1) ||| ((c >>> 1 &&& 1) <<< 5) ||| ((c >>> 2 &&& 1) <<< 10) ||| ((c >>> 3 &&& 1) <<< 15) |||
    ((c >>> 4 &&& 1) <<< 20)

@[expose] def gtUT (x : Nat) : Nat :=
  (x &&& 1) ||| ((x >>> 5 &&& 1) <<< 1) ||| ((x >>> 10 &&& 1) <<< 2) ||| ((x >>> 15 &&& 1) <<< 3) |||
    ((x >>> 20 &&& 1) <<< 4)

theorem gtUT_lt (x : Nat) : gtUT x < 32 := by
  have h : ∀ y s, s < 5 → (y &&& 1) <<< s < 2 ^ 5 := fun y s hs => by
    rw [Nat.shiftLeft_eq]
    have : y &&& 1 ≤ 1 := Nat.and_le_right
    have : 2 ^ s ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have : (y &&& 1) * 2 ^ s ≤ 1 * 2 ^ 4 := Nat.mul_le_mul (by omega) this
    simp at this ⊢
    omega
  have h0 : x &&& 1 < 2 ^ 5 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h0
    (h _ 1 (by omega))) (h _ 2 (by omega))) (h _ 3 (by omega))) (h _ 4 (by omega))

theorem sprUT_lt : ∀ c < 32, sprUT c < 2 ^ 25 := by decide

theorem tbUT_one (q : Nat) : Nat.testBit 1 q = decide (0 = q) := by
  rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]

theorem andUT_eq (x : Nat) : x &&& 1082401 = sprUT (gtUT x) := by
  refine Nat.eq_of_testBit_eq fun p => ?_
  by_cases hp : p < 25
  · interval_cases p <;> simp [-Nat.and_one_is_mod, sprUT, gtUT, Nat.testBit_or, Nat.testBit_and,
      tbUT_one, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, mUT_bit]
  · have hpow : 2 ^ 25 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow x
      (by decide : 1082401 < 2 ^ 25)) hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (sprUT_lt _ (gtUT_lt x)) hpow)]

theorem sprUT_31 : ∀ c < 32, sprUT c * 31 = spUT (sprUT c) := by decide

theorem mulUT_31 (x : Nat) : (x &&& 1082401) * 31 = spUT (x &&& 1082401) := by
  rw [andUT_eq]
  exact sprUT_31 _ (gtUT_lt x)

theorem mtUT_bit {r : Nat} (hr : r < 32) (b j : Nat) {p : Nat} (hp : p < 25) :
    (mtUT r b j).testBit p = ((spUT (Nat.land (Nat.shiftRight b j) 1082401)).testBit p &&
      r.testBit (p % 5)) := by
  rw [mtUT, cv_land, Nat.testBit_and, Nat.mul_eq, Nat.mul_eq, cv_land, mulUT_31, rUT_bit r hr p hp]

theorem mulUT_eq (a b : Nat) : mulUT a b = mulC a b := by
  refine eq_of_bits (mulUT_lt a b) (mulC_lt a b) fun p hp => ?_
  have hr : ∀ i, i < 5 → ∀ k, k < 5 →
      (mulC a b).testBit (5 * i + k) = (rowN (mulC a b) i).testBit k :=
    fun i _ k hk => by rw [rowN_eq, rk_bit _ _ hk]
  obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < 5 ∧ k < 5 ∧ p = 5 * i + k :=
    ⟨p / 5, p % 5, by omega, by omega, by omega⟩
  rw [hr i hi k hk]
  simp only [mulUT, cv_xor, Nat.testBit_xor, mtUT_bit (r0_lt a) b _ hp, mtUT_bit (r1_lt a) b _ hp,
    mtUT_bit (r2_lt a) b _ hp, mtUT_bit (r3_lt a) b _ hp, mtUT_bit (r4_lt a) b _ hp]
  interval_cases i <;> interval_cases k <;>
    simp [-Nat.testBit_zero, spUT, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_and, mUT_bit, rowN_0, rowN_1, rowN_2, rowN_3, rowN_4, r0_mulC, r1_mulC, r2_mulC,
      r3_mulC, r4_mulC, vm, vm5_testBit, r0_bit, r1_bit, r2_bit, r3_bit, r4_bit, Bool.and_comm]

theorem powUT_eq (a b : Nat) : ∀ k, powUT (mulUT a b) k = powC (mulC a b) (k + 1)
  | 0 => by
    change mulUT a b = mulC (mulC a b) idC
    rw [mulUT_eq, mulC_idC (mulC_lt a b)]
  | k + 1 => by
    change mulUT (mulUT a b) (powUT (mulUT a b) k) = mulC (mulC a b) (powC (mulC a b) (k + 1))
    rw [powUT_eq a b k, mulUT_eq, mulUT_eq]

theorem gathUT_lt (c : Nat) : gathUT c < 128 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.add acc (Nat.shiftLeft 1 j))
        (bitB c (nthL pivUT j))) n : Nat) < 2 ^ n := by
    intro n
    induction n with
    | zero => exact Nat.one_pos
    | succ n ih =>
      simp only [natRec_succ]
      rw [Nat.pow_succ]
      cases bitB c (nthL pivUT n)
      · exact Nat.lt_of_lt_of_le ih (by omega)
      · change _ + 1 <<< n < _
        rw [Nat.one_shiftLeft]
        omega
  exact key 7

theorem goodUT_good (hc : cenUTOK = true) {h : Nat} (hg : goodUT h = true) : good h = true := by
  rw [goodUT, Bool.and_eq_true] at hg
  obtain ⟨hb, hv⟩ := hg
  have he : comboUT (gathUT h) = h := Nat.eq_of_beq_eq_true hb
  have hp := rec_all cenUTP 128 hc (gathUT h) (gathUT_lt h)
  rw [cenUTP, he] at hp
  simp only [mulF_eq] at hp
  unfold good
  rw [hp, hv]
  rfl

theorem certsOK_mem {X : List Nat} :
    ∀ {B : List (List Nat)}, List.rec (motive := fun _ => Bool) true
      (fun l _ acc => Bool.rec (motive := fun _ => Bool) false acc (allL (certOK X) l)) B = true →
      ∀ l ∈ B, allL (certOK X) l = true
  | [], _, l, hl => absurd hl List.not_mem_nil
  | a :: B, h, l, hl => by
    have h' : Bool.rec (motive := fun _ => Bool) false (List.rec (motive := fun _ => Bool) true
        (fun l _ acc => Bool.rec (motive := fun _ => Bool) false acc (allL (certOK X) l)) B)
        (allL (certOK X) a) = true := h
    cases hfa : allL (certOK X) a <;> rw [hfa] at h'
    · exact absurd h' Bool.false_ne_true
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact hfa
      · exact certsOK_mem h' l hl

theorem nthL_X {X : List Nat} (hX : x0OK X = true) {i : Nat} (hi : i < 24) (g : Nat) :
    nthL X i = (x0W i).evalC g := by
  have hX' : X = x0Words.toList.map evalList := beq_iff_eq.mp hX
  have hs : i < x0Words.size := hi
  rw [nthL_eq, hX', x0W, Wd.evalC_ofList, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  rfl

theorem cert_sound {X : List Nat} {B : List (List Nat)} (h : certsOK X B = true)
    (hX : x0OK X = true) : ∀ l ∈ B, ∀ e ∈ l, ∃ ω : Wd, good (ω.evalC (codeE e)) = true := by
  intro l hl e he
  rw [certsOK, Bool.and_eq_true] at h
  have h1 := allL_mem (certsOK_mem h.2 l hl) e he
  unfold certOK at h1
  cases hc : (Nat.blt (Nat.shiftRight e 46) 24 && Nat.blt (Nat.land (Nat.shiftRight e 36) 31) 24 &&
      Nat.blt (Nat.land (Nat.shiftRight e 25) 31) 24) <;> rw [hc] at h1
  · exact absurd h1 Bool.false_ne_true
  · simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    obtain ⟨⟨hz, h2⟩, h3⟩ := hc
    refine ⟨.mul (x0W (Nat.shiftRight e 46)) (.pow (.mul (x0W (Nat.land (Nat.shiftRight e 36) 31))
      (.pow (.mul (x0W (Nat.land (Nat.shiftRight e 25) 31)) .var)
        (Nat.pred (Nat.land (Nat.shiftRight e 30) 63) + 1)))
        (Nat.pred (Nat.land (Nat.shiftRight e 41) 31) + 1)), ?_⟩
    have h1' : goodUT (mulUT (nthL X (Nat.shiftRight e 46))
        (powUT (mulUT (nthL X (Nat.land (Nat.shiftRight e 36) 31))
          (powUT (mulUT (nthL X (Nat.land (Nat.shiftRight e 25) 31)) (codeE e))
            (Nat.pred (Nat.land (Nat.shiftRight e 30) 63))))
          (Nat.pred (Nat.land (Nat.shiftRight e 41) 31)))) = true := h1
    have h1'' := goodUT_good h.1 h1'
    rw [powUT_eq, powUT_eq] at h1''
    simp only [mulUT_eq, nthL_X hX hz (codeE e), nthL_X hX h2 (codeE e),
      nthL_X hX h3 (codeE e)] at h1''
    simpa only [Wd.evalC] using h1''

section CoverW

open CFSG.KC.F4M3B (frcN_eq frc_eq)

theorem rwL_bit (l p i k : Nat) : (rwL l p i).testBit k =
    (decide (k < 4) && p.testBit (4 * i + k) || decide (k = 4) && (p.testBit 20 && l.testBit i)) := by
  unfold rwL
  rw [cv_lor, Nat.testBit_or, cv_land, Nat.testBit_and, cv_shr, Nat.testBit_shiftRight, Nat.mul_eq,
    ← testBit_eq_bitB, ← testBit_eq_bitB]
  have h15 : (15 : Nat) = 2 ^ 4 - 1 := rfl
  have h16 : (16 : Nat) = 2 ^ 4 := rfl
  have t16 : (16 : Nat).testBit k = decide (k = 4) := by
    rw [h16, Nat.testBit_two_pow]
    exact decide_eq_decide.mpr eq_comm
  rw [h15, Nat.testBit_two_pow_sub_one]
  cases p.testBit 20 <;> cases l.testBit i <;> simp [t16, Bool.and_comm]

theorem rwL_lt (l p i : Nat) : rwL l p i < 32 := by
  unfold rwL
  rw [cv_lor, cv_land]
  refine Nat.or_lt_two_pow (n := 5) (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) ?_
  cases bitB p 20 && bitB l i <;> decide

theorem expW_rows (l p : Nat) : r0 (expW l p) = rwL l p 0 ∧ r1 (expW l p) = rwL l p 1 ∧
    r2 (expW l p) = rwL l p 2 ∧ r3 (expW l p) = rwL l p 3 ∧ r4 (expW l p) = rwL l p 4 := by
  have h := fun i => rwL_lt l p i
  exact ⟨r0_ofRows (h 0) (h 1) (h 2) (h 3) (h 4), r1_ofRows (h 0) (h 1) (h 2) (h 3) (h 4),
    r2_ofRows (h 0) (h 1) (h 2) (h 3) (h 4), r3_ofRows (h 0) (h 1) (h 2) (h 3) (h 4),
    r4_ofRows (h 0) (h 1) (h 2) (h 3) (h 4)⟩

theorem expW_lt (l p : Nat) : expW l p < N :=
  ofRows_lt (rwL_lt l p 0) (rwL_lt l p 1) (rwL_lt l p 2) (rwL_lt l p 3) (rwL_lt l p 4)

theorem expW_lt' (l p : Nat) : expW l p < 2 ^ 25 := expW_lt l p

theorem rwL_xor (l p q i : Nat) : rwL l (p ^^^ q) i = rwL l p i ^^^ rwL l q i :=
  Nat.eq_of_testBit_eq fun k => by
    rw [Nat.testBit_xor, rwL_bit, rwL_bit, rwL_bit, Nat.testBit_xor, Nat.testBit_xor]
    rcases Nat.lt_or_ge k 4 with h1 | h1
    · have h2 : decide (k = 4) = false := by simp; omega
      simp [decide_eq_true h1, h2]
    · have h1' : decide (k < 4) = false := by simp; omega
      simp only [h1', Bool.false_and, Bool.false_or]
      cases decide (k = 4) <;> cases p.testBit 20 <;> cases q.testBit 20 <;> cases l.testBit i <;>
        rfl

theorem expW_xor (l p q : Nat) : expW l (p ^^^ q) = expW l p ^^^ expW l q := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := expW_rows l (p ^^^ q)
  obtain ⟨b0, b1, b2, b3, b4⟩ := expW_rows l p
  obtain ⟨c0, c1, c2, c3, c4⟩ := expW_rows l q
  refine code_ext (expW_lt l _) (Nat.xor_lt_two_pow (expW_lt' l p) (expW_lt' l q)) ?_ ?_ ?_ ?_ ?_
  · rw [r0_xor, a0, b0, c0, rwL_xor]
  · rw [r1_xor, a1, b1, c1, rwL_xor]
  · rw [r2_xor, a2, b2, c2, rwL_xor]
  · rw [r3_xor, a3, b3, c3, rwL_xor]
  · rw [r4_xor, a4, b4, c4, rwL_xor]

theorem basisW_spec {ops : List Nat} {l g : Nat} (h : basisW ops l g = true) :
    ∀ b < 21, expW l (ptS ops (2 ^ b)) = mulC g (expW l (2 ^ b)) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Bool) true
      (fun b acc => Bool.rec (motive := fun _ => Bool) false acc
        (Nat.beq (expW l (ptS ops (Nat.shiftLeft 1 b))) (mulC g (expW l (Nat.shiftLeft 1 b))))) n :
        Bool) = true → ∀ b < n, expW l (ptS ops (2 ^ b)) = mulC g (expW l (2 ^ b)) := by
    intro n
    induction n with
    | zero => intro _ b hb; omega
    | succ n ih =>
      intro h b hb
      simp only [natRec_succ] at h
      cases hn : Nat.beq (expW l (ptS ops (Nat.shiftLeft 1 n))) (mulC g (expW l (Nat.shiftLeft 1 n)))
        <;> rw [hn] at h
      · exact absurd h Bool.false_ne_true
      · by_cases hbn : b = n
        · subst hbn
          have := Nat.eq_of_beq_eq_true hn
          rwa [cv_shl, Nat.one_shiftLeft] at this
        · exact ih h b (by omega)
  exact key 21 h

theorem basisW_all {ops : List Nat} {l g : Nat} (h : basisW ops l g = true) :
    ∀ p < 2 ^ 21, expW l (ptS ops p) = mulC g (expW l p) :=
  lin_ext (F := fun p => expW l (ptS ops p)) (G := fun p => mulC g (expW l p))
    (fun a b => by simp only [ptS_xor, expW_xor]) (fun a b => by simp only [expW_xor, mulC_xor_r])
    (basisW_spec h) 21 le_rfl

def PW (B : List (List Nat)) (l p : Nat) : Prop :=
  ∃ τ : Wd, ∃ L ∈ B, ∃ e ∈ L, τ.evalC (expW l p) = codeE e

theorem good_gen {B : List (List Nat)} {ops : List Nat} {l i : Nat} (ho : allL opOK ops = true)
    (hb : basisW ops l (genC i) = true) :
    (∀ op ∈ ops, opOK op = true) ∧ ∀ p < 2 ^ 21, PW B l (ptS ops p) → PW B l p := by
  refine ⟨allL_mem ho, fun p hp ⟨τ, L, hL, e, he, hτ⟩ => ⟨τ.subst (.mul (.gen i) .var), L, hL, e, he, ?_⟩⟩
  rw [Wd.evalC_subst, ← hτ, basisW_all hb p hp]
  rfl

theorem lwOK_good {B LW : List (List Nat)} {cl l : Nat} (h : lwOK LW cl l = true) :
    GoodOs (PW B l) (gensW LW cl) := by
  simp only [lwOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, b0⟩, b1⟩, b2⟩, b3⟩ := h
  intro ops hops
  simp only [gensW, List.mem_cons, List.not_mem_nil, or_false] at hops
  rcases hops with rfl | rfl | rfl | rfl
  · exact good_gen (i := 0) o0 b0
  · exact good_gen (i := 1) o1 b1
  · exact good_gen (i := 2) o2 b2
  · exact good_gen (i := 3) o3 b3

theorem nthL_mem {L : List Nat} {o : Nat} (h : nthL L o ≠ 0) : nthL L o ∈ L := by
  rw [nthL_eq] at h ⊢
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases hg : L[o]? with
  | none => rw [hg] at h; exact absurd rfl h
  | some a => exact List.mem_of_getElem? hg

theorem nthLL_eq (L : List (List Nat)) (i : Nat) : nthLL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n

theorem nthLL_mem {L : List (List Nat)} {i : Nat} (h : nthLL L i ≠ []) : nthLL L i ∈ L := by
  rw [nthLL_eq] at h ⊢
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases hg : L[i]? with
  | none => rw [hg] at h; exact absurd rfl h
  | some a => exact List.mem_of_getElem? hg

theorem codeE_lt (e : Nat) : codeE e < N := Nat.and_lt_two_pow (n := 25) e (by decide)

theorem seed_PW {X : List Nat} {B : List (List Nat)} {l j d : Nat} (hX : x0OK X = true)
    (hp : ∀ k < 24, powC (nthL X k) 24 = idC) (hl : ∃ i < 5, l.testBit i = true)
    (h : seedOK X B l j d = true) (hq21 : 1048576 + (1024 * j + Nat.land d 1023) < 2 ^ 21) :
    PW B l (1048576 + (1024 * j + Nat.land d 1023)) := by
  simp only [seedOK, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨hk, he⟩ := h
  have he' := Nat.eq_of_beq_eq_true he
  rw [mulUT_eq] at he'
  generalize hq : 1048576 + (1024 * j + Nat.land d 1023) = q at he' hq21
  have hq20 : q.testBit 20 = true := by
    have e20 : (2 : Nat) ^ 20 = 1048576 := rfl
    have e21 : (2 : Nat) ^ 21 = 2097152 := rfl
    rw [e21] at hq21
    rw [Nat.testBit_eq_decide_div_mod_eq, e20, decide_eq_true_eq]
    omega
  generalize hb : nthL (nthLL B (Nat.shiftRight d 27)) (Nat.land (Nat.shiftRight d 15) 4095) = b at he'
  generalize hk' : Nat.land (Nat.shiftRight d 10) 31 = k at he' hk
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi, hli⟩ := hl
    have h0 : codeE 0 = 0 := rfl
    rw [h0] at he'
    have hz : mulC 0 (nthL X k) = 0 :=
      lin_zero (F := fun a => mulC a (nthL X k)) (fun a b => mulC_xor_l a b _)
    rw [hz] at he'
    obtain ⟨a0, a1, a2, a3, a4⟩ := expW_rows l q
    have hr := rwL_bit l q i 4
    simp only [hq20, hli] at hr
    interval_cases i
    · rw [← a0, he'] at hr
      simp [r0] at hr
    · rw [← a1, he'] at hr
      simp [r1] at hr
    · rw [← a2, he'] at hr
      simp [r2] at hr
    · rw [← a3, he'] at hr
      simp [r3] at hr
    · rw [← a4, he'] at hr
      simp [r4] at hr
  have hLne : nthLL B (Nat.shiftRight d 27) ≠ [] := by
    intro hn
    rw [hn] at hb
    exact hb0 hb.symm
  refine ⟨.mul .var (.pow (x0W k) 23), _, nthLL_mem hLne, b, by rw [← hb]; exact nthL_mem (hb ▸ hb0), ?_⟩
  have hy := nthL_X hX hk (expW l q)
  simp only [Wd.evalC]
  rw [← hy, he', mulC_assoc]
  have h24 : mulC (nthL X k) (powC (nthL X k) 23) = idC := hp k hk
  rw [h24, mulC_idC (codeE_lt b)]

theorem ofC_expW {Ms : List Nat}
    (hMs : ∀ j < 21, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 21) && x.testBit j))
    {l p : Nat} (hp : p < 2 ^ 21) : (matW Ms l).map (fun n => n.testBit p) = ofC (expW l p) := by
  have hM : ∀ j, j < 21 → (nthL Ms j).testBit p = p.testBit j := fun j hj => by
    rw [hMs j hj, decide_eq_true hp, Bool.true_and]
  have hE : ∀ i, (Bool.rec (motive := fun _ => Nat) 0 (nthL Ms 20) (bitB l i)).testBit p =
      (p.testBit 20 && l.testBit i) := fun i => by
    rw [← testBit_eq_bitB]
    cases l.testBit i
    · simp
    · simp [hM 20 (by omega)]
  obtain ⟨a0, a1, a2, a3, a4⟩ := expW_rows l p
  simp (disch := omega) only [matW, rowW, M5.map, R5.map, ofC, rowB, a0, a1, a2, a3, a4, rwL_bit, hM,
    hE, Nat.mul_eq, Nat.add_eq]
  simp

theorem covW_sound {X : List Nat} {B LW S : List (List Nat)} {cl l : Nat}
    (h : covW X B LW cl l S = true) (hX : x0OK X = true)
    (hp : ∀ k < 24, powC (nthL X k) 24 = idC) (hl : ∃ i < 5, l.testBit i = true) {p : Nat}
    (hp21 : p < 2 ^ 21) (hns : nonsing (expW l p) = true) : PW B l p := by
  unfold covW at h
  generalize hT : Nat.sub (Nat.shiftLeft 1 2097152) 1 = t at h
  have ht : t.testBit p = true := by
    rw [← hT]
    exact allOnes_bit hp21
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hw, hs⟩, hm⟩ := h
  rw [frc_eq] at hm
  obtain ⟨Ms, hMs, hm⟩ := msW_spec hm
  simp only [frc_eq] at hm
  have hbit := congrArg (fun x => x.testBit p) (Nat.eq_of_beq_eq_true hm)
  have hnsP : (nsK (natOps t) (matW Ms l)).testBit p = nonsing (expW l p) := by
    rw [nsK_eq _ (natOps_bd t), nsD_map (natOps t) boolOps (fun n => n.testBit p)
      (fun p q => Nat.testBit_and p q _) (fun p q => Nat.testBit_or p q _)
      (fun p q => Nat.testBit_xor p q _) ht (Nat.zero_testBit p), ofC_expW hMs hp21,
      Bool.eq_iff_iff, nsD_ofC, nonsing_iff]
    exact ⟨fun h v h0 h1 => h v h0 (by omega), fun h v h0 h1 => h v h0 (by omega)⟩
  simp only [cv_land, cv_xor, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hnsP, hns, ht]
    at hbit
  have h0 : CovInv (PW B l) (Nat.shiftLeft (indS S) 1048576) := fun q hq hb => by
    rw [cv_shl, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨j, d, hd, hqd⟩ := indS_bit hs hb.2
    have e : q = 1048576 + (1024 * j + Nat.land d 1023) := by omega
    rw [e]
    exact seed_PW hX hp hl (by simpa using hd) (by rw [← e]; exact hq)
  exact roundsS_inv hMs (lwOK_good hw) 3 h0 p hp21 (by simpa using hbit)

theorem anyN_spec {f : Nat → Bool} : ∀ {n : Nat}, anyN f n = true → ∃ i < n, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool) (f n) true (anyN f n) = true at h
    cases ha : anyN f n
    · rw [ha] at h
      exact ⟨n, by omega, h⟩
    · obtain ⟨i, hi, hf⟩ := anyN_spec ha
      exact ⟨i, by omega, hf⟩

def idxW (c : Nat) : Nat :=
  r0 c % 16 ||| (r1 c % 16) <<< 4 ||| (r2 c % 16) <<< 8 ||| (r3 c % 16) <<< 12 |||
    (r4 c % 16) <<< 16 ||| 1048576

theorem tb16 (x j : Nat) : (x % 16).testBit j = (decide (j < 4) && x.testBit j) :=
  Nat.testBit_mod_two_pow x 4 j

theorem t20 (j : Nat) : (1048576 : Nat).testBit j = decide (j = 20) := by
  have e : (1048576 : Nat) = 2 ^ 20 := rfl
  rw [e, Nat.testBit_two_pow]
  exact decide_eq_decide.mpr eq_comm

theorem idxW_bit (c : Nat) {i k : Nat} (hi : i < 5) (hk : k < 4) :
    (idxW c).testBit (4 * i + k) = (rowN c i).testBit k := by
  interval_cases i <;> interval_cases k <;>
    simp [idxW, Nat.testBit_or, Nat.testBit_shiftLeft, tb16, t20, rowN_0, rowN_1, rowN_2, rowN_3,
      rowN_4]

theorem idxW_20 (c : Nat) : (idxW c).testBit 20 = true := by
  simp [idxW, Nat.testBit_or, t20]

theorem idxW_lt (c : Nat) : idxW c < 2 ^ 21 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    have h1 : ¬ i < 4 := by omega
    have h2 : ¬ i - 4 < 4 := by omega
    have h3 : ¬ i - 8 < 4 := by omega
    have h4 : ¬ i - 12 < 4 := by omega
    have h5 : ¬ i - 16 < 4 := by omega
    have h6 : ¬ i = 20 := by omega
    simp [idxW, Nat.testBit_or, Nat.testBit_shiftLeft, tb16, t20, h1, h2, h3, h4, h5, h6]

theorem rwL_idxW {c l i : Nat} (hi : i < 5) (h4 : (rowN c i).testBit 4 = l.testBit i) :
    rwL l (idxW c) i = rowN c i := by
  have hr : rowN c i < 32 := by rw [rowN_eq]; omega
  refine Nat.eq_of_testBit_eq fun k => ?_
  rw [rwL_bit]
  by_cases hk : k < 4
  · have hk4 : decide (k = 4) = false := by simp; omega
    rw [decide_eq_true hk, hk4, Bool.true_and, Bool.false_and, Bool.or_false, idxW_bit c hi hk]
  · by_cases hk' : k = 4
    · subst hk'
      simp [idxW_20, h4]
    · have hk5 : rowN c i < 2 ^ k := Nat.lt_of_lt_of_le hr
        (by have := Nat.pow_le_pow_right (n := 2) (by omega) (show 5 ≤ k by omega); simpa using this)
      rw [Nat.testBit_lt_two_pow hk5]
      simp [hk, hk']

theorem expW_idxW {c l : Nat} (hc : c < N) (h4 : ∀ i < 5, (rowN c i).testBit 4 = l.testBit i) :
    expW l (idxW c) = c := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := expW_rows l (idxW c)
  refine code_ext (expW_lt _ _) hc ?_ ?_ ?_ ?_ ?_
  · rw [a0, rwL_idxW (by omega) (h4 0 (by omega)), rowN_0]
  · rw [a1, rwL_idxW (by omega) (h4 1 (by omega)), rowN_1]
  · rw [a2, rwL_idxW (by omega) (h4 2 (by omega)), rowN_2]
  · rw [a3, rwL_idxW (by omega) (h4 3 (by omega)), rowN_3]
  · rw [a4, rwL_idxW (by omega) (h4 4 (by omega)), rowN_4]

theorem col_mulC {a a' : Nat} (y : Nat) (h : ∀ j < 5, (rowN a j).testBit 4 = (rowN a' j).testBit 4)
    {i : Nat} (hi : i < 5) : (rowN (mulC a y) i).testBit 4 = (rowN (mulC a' y) i).testBit 4 := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  simp only [rowN_0, rowN_1, rowN_2, rowN_3, rowN_4] at h0 h1 h2 h3 h4
  interval_cases i <;>
    simp only [rowN_0, rowN_1, rowN_2, rowN_3, rowN_4, r0_mulC, r1_mulC, r2_mulC, r3_mulC,
      r4_mulC, vm, vm5_testBit, h0, h1, h2, h3, h4]

theorem nonsing_mulC {a y : Nat} (ha : nonsing a = true) (hy : nonsing y = true) :
    nonsing (mulC a y) = true := by
  rw [nonsing_iff] at ha hy ⊢
  intro v h0 h1 hv
  rw [vm_mulC] at hv
  exact hy v h0 h1 (Nat.eq_zero_of_not_pos fun hp => ha _ hp (vm_lt v y) hv)

theorem colN_row (c : Nat) {j : Nat} (hj : j < 5) : (colN c 4).testBit j = (rowN c j).testBit 4 := by
  obtain ⟨b0, b1, b2, b3, b4⟩ := colN_bit c (m := 4) (by omega)
  interval_cases j
  · rw [b0, rowN_0]
  · rw [b1, rowN_1]
  · rw [b2, rowN_2]
  · rw [b3, rowN_3]
  · rw [b4, rowN_4]

theorem rowN_expW (l p : Nat) {i : Nat} (hi : i < 5) : rowN (expW l p) i = rwL l p i := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := expW_rows l p
  interval_cases i
  · rw [rowN_0, a0]
  · rw [rowN_1, a1]
  · rw [rowN_2, a2]
  · rw [rowN_3, a3]
  · rw [rowN_4, a4]

theorem nthL_memX {X : List Nat} (hX : x0OK X = true) {k : Nat} (hk : k < 24) : nthL X k ∈ X := by
  have hX' : X = x0Words.toList.map evalList := beq_iff_eq.mp hX
  have hl : X.length = 24 := by rw [hX', List.length_map, Array.length_toList]; rfl
  rw [nthL_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem cover_sound {X : List Nat} {B LW S0 S1 S2 S3 : List (List Nat)}
    (h0 : covW X B LW 0 1 S0 = true) (h1 : covW X B LW 1 4 S1 = true)
    (h2 : covW X B LW 2 6 S2 = true) (h3 : covW X B LW 3 20 S3 = true) (hr : redOK X = true)
    (hX : x0OK X = true) {c : Nat} (_hc : c < N) (hns : nonsing c = true) (hst : stabW4 c = false) :
    ∃ τ : Wd, ∃ l ∈ B, ∃ e ∈ l, τ.evalC c = codeE e := by
  rw [redOK, Bool.and_eq_true] at hr
  obtain ⟨hy, hm⟩ := hr
  have hyX : ∀ k < 24, nonsing (nthL X k) = true ∧ powC (nthL X k) 24 = idC := fun k hk => by
    have := allL_mem hy _ (nthL_memX hX hk)
    rw [Bool.and_eq_true, powF_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hp : ∀ k < 24, powC (nthL X k) 24 = idC := fun k hk => (hyX k hk).2
  have hmc : ∀ j < 5, (colN c 4 % 32).testBit j = (rowN c j).testBit 4 := fun j hj => by
    have h32 : (32 : Nat) = 2 ^ 5 := rfl
    rw [h32, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, colN_row c hj]
  have hm' := rec_all (fun m => Nat.beq (Nat.land m 15) 0 || anyN (fun i =>
    Nat.beq (colN (mulC (expW m 1048576) (nthL X (Nat.mod i 24))) 4) (nthL repL (Nat.div i 24))) 96)
    32 hm (colN c 4 % 32) (Nat.mod_lt _ (by omega))
  simp only [Bool.or_eq_true] at hm'
  rcases hm' with hz | ha
  · exfalso
    have hz' := congrArg (fun x => x.testBit) (Nat.eq_of_beq_eq_true hz)
    have hb : ∀ j < 4, (colN c 4).testBit j = false := fun j hj => by
      have := congrFun hz' j
      simp only [cv_land, Nat.testBit_and, Nat.zero_testBit] at this
      have h15 : (15 : Nat).testBit j = true := by interval_cases j <;> rfl
      rw [h15, Bool.and_true, hmc j (by omega), ← colN_row c (by omega)] at this
      exact this
    rw [stabW4_eq] at hst
    have e0 := hb 0 (by omega)
    have e1 := hb 1 (by omega)
    have e2 := hb 2 (by omega)
    have e3 := hb 3 (by omega)
    rw [colN_row c (by omega), rowN_0, r0_bit c (by omega)] at e0
    rw [colN_row c (by omega), rowN_1, r1_bit c (by omega)] at e1
    rw [colN_row c (by omega), rowN_2, r2_bit c (by omega)] at e2
    rw [colN_row c (by omega), rowN_3, r3_bit c (by omega)] at e3
    simp [e0, e1, e2, e3] at hst
  · obtain ⟨i, hi, hf⟩ := anyN_spec ha
    have e1 : Nat.div i 24 = i / 24 := rfl
    have e2 : Nat.mod i 24 = i % 24 := rfl
    rw [e1, e2] at hf
    have hk : i % 24 < 24 := Nat.mod_lt _ (by omega)
    have hcl : i / 24 < 4 := by omega
    generalize i % 24 = k at hk hf
    generalize i / 24 = cl at hcl hf
    have hl := Nat.eq_of_beq_eq_true hf
    set y := nthL X k with hyd
    set c' := mulC c y with hc'
    have hrow : ∀ j < 5, (rowN c' j).testBit 4 = (nthL repL cl).testBit j := fun j hj => by
      rw [← hl, colN_row _ hj]
      refine col_mulC y (fun j' hj' => ?_) hj
      rw [rowN_expW _ _ hj', rwL_bit, ← hmc j' hj']
      simp [t20]
    have hrec := expW_idxW (mulC_lt c y) hrow
    have hns' := nonsing_mulC hns (hyX k hk).1
    rw [← hrec] at hns'
    have hP : PW B (nthL repL cl) (idxW c') := by
      interval_cases cl
      · exact covW_sound h0 hX hp ⟨0, by omega, rfl⟩ (idxW_lt _) hns'
      · exact covW_sound h1 hX hp ⟨2, by omega, rfl⟩ (idxW_lt _) hns'
      · exact covW_sound h2 hX hp ⟨1, by omega, rfl⟩ (idxW_lt _) hns'
      · exact covW_sound h3 hX hp ⟨2, by omega, rfl⟩ (idxW_lt _) hns'
    obtain ⟨τ, L, hL, e, he, hτ⟩ := hP
    refine ⟨τ.subst (.mul .var (x0W k)), L, hL, e, he, ?_⟩
    rw [Wd.evalC_subst, ← hτ, hrec]
    simp only [Wd.evalC, hyd, nthL_X hX hk c]

end CoverW

section Cent

open CFSG.KC.F4M3B (frc_eq pln pln_bit)

theorem allR_spec {f : Nat → Bool} (h : allR f = true) {r : Nat} (hr : r < 32) : f r = true :=
  rec_all f 32 h r hr

theorem gathK_lt (c : Nat) : gathK c < 2 ^ 13 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.add acc (Nat.shiftLeft 1 j))
        (bitB c (nthL pivK j))) n : Nat) < 2 ^ n := by
    intro n
    induction n with
    | zero => exact Nat.one_pos
    | succ n ih =>
      simp only [natRec_succ]
      rw [Nat.pow_succ]
      cases bitB c (nthL pivK n)
      · exact Nat.lt_of_lt_of_le ih (by omega)
      · change _ + 1 <<< n < _
        rw [Nat.one_shiftLeft]
        omega
  exact key 13

theorem plC_bit (b : Nat) {p : Nat} (hp : p < 2 ^ 13) : (plC b).testBit p = (comboK p).testBit b := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (pln j 13))
        (bitB (nthL kB j) b)) n : Nat).testBit p =
      (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (nthL kB j))
        (bitB p j)) n : Nat).testBit b := by
    intro n
    have hp' : p < 8192 := hp
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 := testBit_eq_bitB (nthL kB n) b
      have e2 := testBit_eq_bitB p n
      have hpl : (pln n 13).testBit p = p.testBit n := by
        rw [pln_bit]
        simp [hp']
      cases h1 : bitB (nthL kB n) b <;> cases h2 : bitB p n <;>
        simp only [cv_xor, Nat.testBit_xor, ih, hpl, ← e1, ← e2, h1, h2] <;>
        simp_all
  exact key 13

@[expose] noncomputable def PC : M5 Nat :=
  ⟨⟨plC (Nat.mul 5 0), plC (Nat.add (Nat.mul 5 0) 1), plC (Nat.add (Nat.mul 5 0) 2),
      plC (Nat.add (Nat.mul 5 0) 3), plC (Nat.add (Nat.mul 5 0) 4)⟩,
    ⟨plC (Nat.mul 5 1), plC (Nat.add (Nat.mul 5 1) 1), plC (Nat.add (Nat.mul 5 1) 2),
      plC (Nat.add (Nat.mul 5 1) 3), plC (Nat.add (Nat.mul 5 1) 4)⟩,
    ⟨plC (Nat.mul 5 2), plC (Nat.add (Nat.mul 5 2) 1), plC (Nat.add (Nat.mul 5 2) 2),
      plC (Nat.add (Nat.mul 5 2) 3), plC (Nat.add (Nat.mul 5 2) 4)⟩,
    ⟨plC (Nat.mul 5 3), plC (Nat.add (Nat.mul 5 3) 1), plC (Nat.add (Nat.mul 5 3) 2),
      plC (Nat.add (Nat.mul 5 3) 3), plC (Nat.add (Nat.mul 5 3) 4)⟩,
    ⟨plC (Nat.mul 5 4), plC (Nat.add (Nat.mul 5 4) 1), plC (Nat.add (Nat.mul 5 4) 2),
      plC (Nat.add (Nat.mul 5 4) 3), plC (Nat.add (Nat.mul 5 4) 4)⟩⟩

theorem PC_map {p : Nat} (hp : p < 2 ^ 13) : PC.map (fun n => n.testBit p) = ofC (comboK p) := by
  simp (disch := omega) only [PC, M5.map, R5.map, plC_bit _ hp, ofC, rowB, Nat.add_eq,
    Nat.mul_eq, r0_bit, r1_bit, r2_bit, r3_bit, r4_bit]

theorem bit_of_sliceC {F : Ops Nat → M5 Nat → Nat} {G : M5 Bool → Bool}
    (hFG : ∀ t i, t.testBit i = true → ∀ A, (F (natOps t) A).testBit i = G (A.map (·.testBit i)))
    (h : sliceC F = true) {p : Nat} (hp : p < 2 ^ 13) : G (ofC (comboK p)) = true := by
  have h1 : Nat.beq (F (natOps (Nat.sub (Nat.pow 2 (Nat.pow 2 13)) 1)) PC)
      (Nat.sub (Nat.pow 2 (Nat.pow 2 13)) 1) = true := by
    simp only [sliceC, plKC, rowPC, frc_eq] at h
    exact h
  have key : ∀ m, Nat.beq (F (natOps (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1)) PC)
      (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1) = true →
      ∃ T, (∀ i, i < 2 ^ m → T.testBit i = true) ∧ F (natOps T) PC = T :=
    fun m h => ⟨_, fun i hi => tT_bit m hi, Nat.eq_of_beq_eq_true h⟩
  obtain ⟨T, hT, h3⟩ := key 13 h1
  have h2 := congrArg (fun n => n.testBit p) h3
  rw [hFG _ _ (hT p hp), PC_map hp, hT p hp] at h2
  exact h2

theorem vm5_t0 (a0 a1 a2 a3 a4 : Nat) : vm5 1 a0 a1 a2 a3 a4 = vm5 1 a0 0 0 0 0 := by
  simp [vm5, Nat.testBit]
theorem vm5_t1 (a0 a1 a2 a3 a4 : Nat) : vm5 2 a0 a1 a2 a3 a4 = vm5 2 a0 a1 0 0 0 := by
  simp [vm5, Nat.testBit]
theorem vm5_t2 (a0 a1 a2 a3 a4 : Nat) : vm5 6 a0 a1 a2 a3 a4 = vm5 6 a0 a1 a2 0 0 := by
  simp [vm5, Nat.testBit]
theorem vm5_t3 (a0 a1 a2 a3 a4 : Nat) : vm5 9 a0 a1 a2 a3 a4 = vm5 9 a0 a1 a2 a3 0 := by
  simp [vm5, Nat.testBit]

theorem cuvR_of {c : Nat} (huv : mulC c uvC = mulC uvC c) :
    cuvR 0 (r0 c) (r0 c) 0 0 0 0 = true ∧ cuvR 1 (r1 c) (r0 c) (r1 c) 0 0 0 = true ∧
    cuvR 2 (r2 c) (r0 c) (r1 c) (r2 c) 0 0 = true ∧
    cuvR 3 (r3 c) (r0 c) (r1 c) (r2 c) (r3 c) 0 = true ∧
    cuvR 4 (r4 c) (r0 c) (r1 c) (r2 c) (r3 c) (r4 c) = true := by
  have e0 := congrArg r0 huv
  have e1 := congrArg r1 huv
  have e2 := congrArg r2 huv
  have e3 := congrArg r3 huv
  have e4 := congrArg r4 huv
  simp only [r0_mulC, r1_mulC, r2_mulC, r3_mulC, r4_mulC, vm] at e0 e1 e2 e3 e4
  have u0 : r0 uvC = 1 := rfl
  have u1 : r1 uvC = 2 := rfl
  have u2 : r2 uvC = 6 := rfl
  have u3 : r3 uvC = 9 := rfl
  have u4 : r4 uvC = 19 := rfl
  simp only [u0, u1, u2, u3, u4] at e0 e1 e2 e3 e4
  rw [vm5_t0] at e0
  rw [vm5_t1] at e1
  rw [vm5_t2] at e2
  rw [vm5_t3] at e3
  simp only [cuvR, vmF_eq, rowN_0, rowN_1, rowN_2, rowN_3, rowN_4, u0, u1, u2, u3, u4]
  rw [e0, e1, e2, e3, e4]
  exact ⟨Nat.beq_refl _, Nat.beq_refl _, Nat.beq_refl _, Nat.beq_refl _, Nat.beq_refl _⟩

theorem cuvOK_spec (h : cuvOK = true) {c : Nat} (hc : c < N) (huv : mulC c uvC = mulC uvC c) :
    comboK (gathK c) = c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := cuvR_of huv
  have k0 := allR_spec h (r0_lt c)
  simp only [h0, Bool.not_true, Bool.false_or] at k0
  have k1 := allR_spec k0 (r1_lt c)
  simp only [h1, Bool.not_true, Bool.false_or] at k1
  have k2 := allR_spec k1 (r2_lt c)
  simp only [h2, Bool.not_true, Bool.false_or] at k2
  have k3 := allR_spec k2 (r3_lt c)
  simp only [h3, Bool.not_true, Bool.false_or] at k3
  have k4 := allR_spec k3 (r4_lt c)
  simp only [h4, Bool.not_true, Bool.false_or, ofRows_rows hc] at k4
  exact Nat.eq_of_beq_eq_true k4

theorem chk1C_sound (h : sliceC chk1 = true) (hk : cuvOK = true) {c : Nat} (hc : c < N)
    (hns : nonsing c = true) (huv : mulC c uvC = mulC uvC c) (ht : mulC c tC = mulC tC c) :
    powC c 64 = idC := by
  have hb := bit_of_sliceC (G := chk1D boolOps) (fun t i ht A => by
    rw [chk1_eq _ (fun y k => F4M3B.frcN_eq y k),
      chk1D_map (natOps t) boolOps (fun n => n.testBit i) (fun p q => Nat.testBit_and p q i)
        (fun p q => Nat.testBit_or p q i) (fun p q => Nat.testBit_xor p q i) ht
        (Nat.zero_testBit i)]) h (gathK_lt c)
  rw [cuvOK_spec hk hc huv] at hb
  exact chk1D_ofC hc hb hns huv ht

theorem chk2C_sound (h : sliceC chk2 = true) (hk : cuvOK = true) {c : Nat} (hc : c < N)
    (hns : nonsing c = true) (huv : mulC c uvC = mulC uvC c) (hD : normD c = true) :
    normV c = true := by
  have hb := bit_of_sliceC (G := chk2D boolOps) (fun t i ht A => by
    rw [chk2_eq _ (fun y k => F4M3B.frcN_eq y k),
      chk2D_map (natOps t) boolOps (fun n => n.testBit i) (fun p q => Nat.testBit_and p q i)
        (fun p q => Nat.testBit_or p q i) (fun p q => Nat.testBit_xor p q i) ht
        (Nat.zero_testBit i)]) h (gathK_lt c)
  rw [cuvOK_spec hk hc huv] at hb
  exact chk2D_ofC hb hns huv hD

end Cent

end CFSG.KC.GL5B

end
