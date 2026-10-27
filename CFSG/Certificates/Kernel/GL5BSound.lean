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

@[expose] noncomputable def PS (m s t : Nat) : M5 Nat :=
  ⟨⟨plS (Nat.mul 5 0) m s t, plS (Nat.add (Nat.mul 5 0) 1) m s t,
      plS (Nat.add (Nat.mul 5 0) 2) m s t, plS (Nat.add (Nat.mul 5 0) 3) m s t,
      plS (Nat.add (Nat.mul 5 0) 4) m s t⟩,
    ⟨plS (Nat.mul 5 1) m s t, plS (Nat.add (Nat.mul 5 1) 1) m s t,
      plS (Nat.add (Nat.mul 5 1) 2) m s t, plS (Nat.add (Nat.mul 5 1) 3) m s t,
      plS (Nat.add (Nat.mul 5 1) 4) m s t⟩,
    ⟨plS (Nat.mul 5 2) m s t, plS (Nat.add (Nat.mul 5 2) 1) m s t,
      plS (Nat.add (Nat.mul 5 2) 2) m s t, plS (Nat.add (Nat.mul 5 2) 3) m s t,
      plS (Nat.add (Nat.mul 5 2) 4) m s t⟩,
    ⟨plS (Nat.mul 5 3) m s t, plS (Nat.add (Nat.mul 5 3) 1) m s t,
      plS (Nat.add (Nat.mul 5 3) 2) m s t, plS (Nat.add (Nat.mul 5 3) 3) m s t,
      plS (Nat.add (Nat.mul 5 3) 4) m s t⟩,
    ⟨plS (Nat.mul 5 4) m s t, plS (Nat.add (Nat.mul 5 4) 1) m s t,
      plS (Nat.add (Nat.mul 5 4) 2) m s t, plS (Nat.add (Nat.mul 5 4) 3) m s t,
      plS (Nat.add (Nat.mul 5 4) 4) m s t⟩⟩

theorem slice_eq (F : Ops Nat → M5 Nat → Nat) (m s : Nat) : slice F m s =
    Nat.beq (F (natOps (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1))
      (PS m s (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1))) (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1) := by
  simp only [slice, plK, rowP, F4M3B.frc_eq]
  rfl

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

theorem allS_slice {F : Ops Nat → M5 Nat → Nat} (h : allS F = true) {s : Nat} (hs : s < 32) :
    slice F 20 s = true := by
  unfold allS at h
  exact rec_all (slice F 20) 32 h s hs

theorem tT_bit (m : Nat) {i : Nat} (hi : i < 2 ^ m) :
    (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1).testBit i = true := by
  rw [Nat.sub_eq, Nat.pow_eq, Nat.pow_eq, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  exact hi

theorem slice_bit (F : Ops Nat → M5 Nat → Nat) (m s : Nat) (h : slice F m s = true) :
    ∃ T, (∀ i, i < 2 ^ m → T.testBit i = true) ∧ F (natOps T) (PS m s T) = T := by
  rw [slice_eq] at h
  exact ⟨_, fun i hi => tT_bit m hi, Nat.eq_of_beq_eq_true h⟩

theorem plS_bit (j s : Nat) {i t : Nat} (hi : i < 2 ^ 20) (ht : t.testBit i = true) :
    (plS j 20 s t).testBit i = (2 ^ 20 * s + i).testBit j := by
  have hi' : i < 1048576 := hi
  unfold plS
  rw [Nat.testBit_two_pow_mul_add _ hi]
  by_cases hj : j < 20
  · have hb : Nat.blt j 20 = true := by simp [Nat.blt_eq, hj]
    rw [hb, if_pos hj, F4M3B.pln_bit]
    simp [hi']
  · have hb : Nat.blt j 20 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact hj
    rw [hb, if_neg hj, ← testBit_eq_bitB, Nat.sub_eq]
    cases hs : s.testBit (j - 20)
    · exact Nat.zero_testBit i
    · exact ht

theorem PS_map (s : Nat) {i t : Nat} (hi : i < 2 ^ 20) (ht : t.testBit i = true) :
    (PS 20 s t).map (fun n => n.testBit i) = ofC (2 ^ 20 * s + i) := by
  simp (disch := omega) only [PS, M5.map, R5.map, plS_bit _ _ hi ht, ofC, rowB, Nat.add_eq,
    Nat.mul_eq, r0_bit, r1_bit, r2_bit, r3_bit, r4_bit]

theorem bit_of_allS {F : Ops Nat → M5 Nat → Nat} {G : M5 Bool → Bool}
    (hFG : ∀ t i, t.testBit i = true → ∀ A, (F (natOps t) A).testBit i = G (A.map (·.testBit i)))
    (h : allS F = true) {c : Nat} (hc : c < N) : G (ofC c) = true := by
  have hs : c / 2 ^ 20 < 32 := by unfold N at hc; omega
  have hi : c % 2 ^ 20 < 2 ^ 20 := Nat.mod_lt _ (by decide)
  have hcs : 2 ^ 20 * (c / 2 ^ 20) + c % 2 ^ 20 = c := Nat.div_add_mod c (2 ^ 20)
  obtain ⟨T, hT, h1⟩ := slice_bit F 20 _ (allS_slice h hs)
  have h2 := congrArg (fun n => n.testBit (c % 2 ^ 20)) h1
  rw [hFG _ _ (hT _ hi), PS_map _ hi (hT _ hi), hcs, hT _ hi] at h2
  exact h2

theorem chk1_bool {c : Nat} (h : allS chk1 = true) (hc : c < N) :
    chk1D boolOps (ofC c) = true :=
  bit_of_allS (fun t i ht A => by
    rw [chk1_eq _ (fun y k => F4M3B.frcN_eq y k),
      chk1D_map (natOps t) boolOps (fun n => n.testBit i) (fun p q => Nat.testBit_and p q i)
        (fun p q => Nat.testBit_or p q i) (fun p q => Nat.testBit_xor p q i) ht
        (Nat.zero_testBit i)])
    h hc

theorem chk2_bool {c : Nat} (h : allS chk2 = true) (hc : c < N) :
    chk2D boolOps (ofC c) = true :=
  bit_of_allS (fun t i ht A => by
    rw [chk2_eq _ (fun y k => F4M3B.frcN_eq y k),
      chk2D_map (natOps t) boolOps (fun n => n.testBit i) (fun p q => Nat.testBit_and p q i)
        (fun p q => Nat.testBit_or p q i) (fun p q => Nat.testBit_xor p q i) ht
        (Nat.zero_testBit i)])
    h hc

theorem chk1_sound (h : allS chk1 = true) {c : Nat} (hc : c < N) (hns : nonsing c = true)
    (huv : mulC c uvC = mulC uvC c) (ht : mulC c tC = mulC tC c) : powC c 64 = idC :=
  chk1D_ofC hc (chk1_bool h hc) hns huv ht

theorem chk2_sound (h : allS chk2 = true) {c : Nat} (hc : c < N) (hns : nonsing c = true)
    (huv : mulC c uvC = mulC uvC c) (hD : normD c = true) : normV c = true :=
  chk2D_ofC (chk2_bool h hc) hns huv hD

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
    Nat.land op 31 < 25 ∧ Nat.shiftRight op 5 < 25 ∧ Nat.land op 31 ≠ Nat.shiftRight op 5 := by
  simp only [opOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  refine ⟨h.1.1, h.1.2, fun he => ?_⟩
  have h2 := h.2
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem tauN_lt {op : Nat} (hop : opOK op = true) {c : Nat} (hc : c < 2 ^ 25) :
    tauN c op < 2 ^ 25 := by
  rw [tauN_eq]
  split
  · exact Nat.xor_lt_two_pow hc (Nat.pow_lt_pow_right (by omega) (opOK_spec hop).1)
  · rw [Nat.xor_zero]
    exact hc

theorem ptS_lt : ∀ {ops : List Nat}, (∀ op ∈ ops, opOK op = true) → ∀ {c : Nat}, c < 2 ^ 25 →
    ptS ops c < 2 ^ 25
  | [], _, _, hc => hc
  | op :: ops, hops, _, hc =>
    tauN_lt (hops op (List.mem_cons.mpr (Or.inl rfl)))
      (ptS_lt (fun o ho => hops o (List.mem_cons_of_mem _ ho)) hc)

theorem tv_core {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {j k : Nat} (hj : j < 25) (hk : k < 25) (hjk : j ≠ k) (I : Nat) {c : Nat} (hc : c < 2 ^ 25) :
    (Nat.lor (Nat.xor I (Nat.land I (nthL Ms k)))
      (Nat.lor (Nat.shiftRight (Nat.land (Nat.land I (nthL Ms k)) (nthL Ms j)) (Nat.shiftLeft 1 j))
        (Nat.shiftLeft (Nat.xor (Nat.land I (nthL Ms k)) (Nat.land (Nat.land I (nthL Ms k))
          (nthL Ms j))) (Nat.shiftLeft 1 j)))).testBit c =
    I.testBit (c ^^^ (if c.testBit k then 2 ^ j else 0)) := by
  simp only [cv_lor, cv_land, cv_xor, cv_shl, cv_shr, Nat.one_shiftLeft, Nat.testBit_or,
    Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hMs k hk,
    hMs j hj]
  have hpj : 2 ^ j < 2 ^ 25 := Nat.pow_lt_pow_right (by omega) hj
  have hcd : decide (c < 2 ^ 25) = true := decide_eq_true hc
  have hf : c ^^^ 2 ^ j < 2 ^ 25 := Nat.xor_lt_two_pow hc hpj
  have hfk : (c ^^^ 2 ^ j).testBit k = c.testBit k := by
    rw [cv_flip_bit]
    simp [hjk]
  cases hcj : c.testBit j
  · rw [cv_flip_add hcj]
    have hfj : (c ^^^ 2 ^ j).testBit j = true := by
      rw [cv_flip_bit, hcj]
      simp
    have hlow : (decide (c ≥ 2 ^ j) && ((I.testBit (c - 2 ^ j) &&
        (decide (c - 2 ^ j < 2 ^ 25) && (c - 2 ^ j).testBit k)) ^^
        (I.testBit (c - 2 ^ j) && (decide (c - 2 ^ j < 2 ^ 25) && (c - 2 ^ j).testBit k) &&
          (decide (c - 2 ^ j < 2 ^ 25) && (c - 2 ^ j).testBit j)))) = false := by
      by_cases hge : c ≥ 2 ^ j
      · have hdj : (c - 2 ^ j).testBit j = true := by
          cases hdj : (c - 2 ^ j).testBit j
          · have e := cv_flip_add hdj
            rw [Nat.add_sub_cancel' hge] at e
            rw [e, cv_flip_bit, hdj] at hcj
            simp at hcj
          · rfl
        have hdl : decide (c - 2 ^ j < 2 ^ 25) = true :=
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
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {op : Nat} (hop : opOK op = true) (I : Nat) {c : Nat} (hc : c < 2 ^ 25) :
    (tvI Ms I op).testBit c = I.testBit (tauN c op) := by
  obtain ⟨hj, hk, hjk⟩ := opOK_spec hop
  rw [tauN_eq, ← tv_core hMs hj hk hjk I hc]
  simp only [tvI, frcN_eq]

theorem imgS_bit {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j)) :
    ∀ {ops : List Nat}, (∀ op ∈ ops, opOK op = true) → ∀ (I : Nat) {c : Nat}, c < 2 ^ 25 →
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

theorem lin_ext {F G : Nat → Nat} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (hG : ∀ a b, G (a ^^^ b) = G a ^^^ G b) (hb : ∀ b < 25, F (2 ^ b) = G (2 ^ b)) :
    ∀ n ≤ 25, ∀ c < 2 ^ n, F c = G c := by
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

theorem basisOK_spec {ops : List Nat} {f : Nat → Nat} (h : basisOK ops f = true) :
    ∀ b < 25, ptS ops (2 ^ b) = f (2 ^ b) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Bool) true
      (fun b acc => Bool.rec (motive := fun _ => Bool) false acc
        (Nat.beq (ptS ops (Nat.shiftLeft 1 b)) (f (Nat.shiftLeft 1 b)))) n : Bool) = true →
      ∀ b < n, ptS ops (2 ^ b) = f (2 ^ b) := by
    intro n
    induction n with
    | zero => intro _ b hb; omega
    | succ n ih =>
      intro h b hb
      simp only [natRec_succ] at h
      cases hn : Nat.beq (ptS ops (Nat.shiftLeft 1 n)) (f (Nat.shiftLeft 1 n)) <;> rw [hn] at h
      · exact absurd h Bool.false_ne_true
      · by_cases hbn : b = n
        · subst hbn
          have := Nat.eq_of_beq_eq_true hn
          rwa [cv_shl, Nat.one_shiftLeft] at this
        · exact ih h b (by omega)
  exact key 25 h

theorem basis_right {ops : List Nat} {g : Nat} (h : basisOK ops (fun c => mulC c g) = true) :
    ∀ c < 2 ^ 25, ptS ops c = mulC c g :=
  lin_ext (F := ptS ops) (G := fun c => mulC c g) (ptS_xor ops) (fun a b => mulC_xor_l a b g)
    (basisOK_spec h) 25 le_rfl

theorem basis_left {ops : List Nat} {g : Nat} (h : basisOK ops (fun c => mulC g c) = true) :
    ∀ c < 2 ^ 25, ptS ops c = mulC g c :=
  lin_ext (F := ptS ops) (G := fun c => mulC g c) (ptS_xor ops) (fun a b => mulC_xor_r g a b)
    (basisOK_spec h) 25 le_rfl

def CovInv (B : List (List Nat)) (U : Nat) : Prop :=
  ∀ c < 2 ^ 25, U.testBit c = true → ∃ τ : Wd, ∃ l ∈ B, ∃ e ∈ l, τ.evalC c = codeE e

def GoodOs (Os : List (List Nat)) : Prop :=
  ∀ ops ∈ Os, (∀ op ∈ ops, opOK op = true) ∧ ∃ w : Wd, ∀ c < 2 ^ 25, ptS ops c = w.evalC c

theorem roundS_inv {B : List (List Nat)} {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {U : Nat} (hU : CovInv B U) : ∀ {Os : List (List Nat)}, GoodOs Os → CovInv B (roundS Ms Os U)
  | [], _ => hU
  | ops :: Os, hOs => by
    intro c hc h
    have e : roundS Ms (ops :: Os) U = roundS Ms Os U ||| imgS Ms U ops :=
      frcN_eq (roundS Ms Os U) (fun acc => Nat.lor acc (imgS Ms U ops))
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact roundS_inv hMs hU (fun o ho => hOs o (List.mem_cons_of_mem _ ho)) c hc h
    · obtain ⟨hops, w, hw⟩ := hOs ops (List.mem_cons.mpr (Or.inl rfl))
      rw [imgS_bit hMs hops U hc] at h
      obtain ⟨τ, l, hl, e, he, hτ⟩ := hU _ (ptS_lt hops hc) h
      refine ⟨τ.subst w, l, hl, e, he, ?_⟩
      rw [Wd.evalC_subst, ← hw c hc, hτ]

theorem roundsS_inv {B : List (List Nat)} {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {Os : List (List Nat)} (hOs : GoodOs Os) :
    ∀ (n : Nat) {U : Nat}, CovInv B U → CovInv B (roundsS Ms Os n U)
  | 0, _, hU => hU
  | n + 1, U, hU => by
    have e : roundsS Ms Os (n + 1) U = roundS Ms Os (roundsS Ms Os n U) :=
      frcN_eq (roundsS Ms Os n U) (fun V => roundS Ms Os V)
    rw [e]
    exact roundS_inv hMs (roundsS_inv hMs hOs n hU) hOs

theorem gens_ok {O : List (List Nat)} {f : Nat → Wd}
    (h : ∀ i < 4, allL opOK (nthLL O i) = true ∧ ∀ c < 2 ^ 25, ptS (nthLL O i) c = (f i).evalC c) :
    GoodOs (gens4 O) := by
  intro ops hops
  have : ∃ i < 4, ops = nthLL O i := by
    simp only [gens4, List.mem_cons, List.not_mem_nil, or_false] at hops
    rcases hops with rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, ⟨3, by omega, rfl⟩]
  obtain ⟨i, hi, rfl⟩ := this
  exact ⟨allL_mem (h i hi).1, f i, (h i hi).2⟩

theorem leafB_bit : ∀ {l : List Nat} {c : Nat}, (leafB l).testBit c = true →
    ∃ e ∈ l, Nat.land e 32767 = c
  | [], c, h => by
    change Nat.testBit 0 c = true at h
    simp at h
  | e :: l, c, h => by
    change (Nat.lor (leafB l) (Nat.shiftLeft 1 (Nat.land e 32767))).testBit c = true at h
    rw [cv_lor, cv_shl, Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨e', he', h'⟩ := leafB_bit h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩
    · exact ⟨e, List.mem_cons.mpr (Or.inl rfl), h⟩

theorem leafB_lt (l : List Nat) {m : Nat} (hm : 32768 ≤ m) : leafB l < 2 ^ m :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases h : (leafB l).testBit i
    · rfl
    · obtain ⟨e, -, he⟩ := leafB_bit h
      rw [cv_land] at he
      have := @Nat.and_le_right e 32767
      omega

theorem indB_bit : ∀ {B : List (List Nat)} {i0 : Nat}, bOK B i0 = true → ∀ {c : Nat},
    (indB B).testBit c = true → ∃ l ∈ B, ∃ e ∈ l, codeE e = c + 32768 * i0
  | [], _, _, c, h => by
    change Nat.testBit 0 c = true at h
    simp at h
  | l :: B, i0, hb, c, h => by
    have hb' : Bool.rec (motive := fun _ => Bool) false (bOK B (i0 + 1))
        (allL (fun e => Nat.beq (Nat.shiftRight (codeE e) 15) i0) l) = true := hb
    cases hl : allL (fun e => Nat.beq (Nat.shiftRight (codeE e) 15) i0) l <;> rw [hl] at hb'
    · exact absurd hb' Bool.false_ne_true
    have ei : indB (l :: B) = Nat.lor (Nat.shiftLeft (indB B) 32768) (leafB l) :=
      frcN_eq (indB B) (fun acc => Nat.lor (Nat.shiftLeft acc 32768) (leafB l))
    rw [ei, cv_lor, cv_shl, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with ⟨hc, h⟩ | h
    · obtain ⟨l', hl', e, he, h'⟩ := indB_bit hb' h
      exact ⟨l', List.mem_cons_of_mem _ hl', e, he, by omega⟩
    · have hc : c < 32768 := by
        by_contra hc
        rw [Nat.testBit_lt_two_pow (leafB_lt l (by omega : 32768 ≤ c))] at h
        exact absurd h Bool.false_ne_true
      obtain ⟨e, he, h'⟩ := leafB_bit h
      have hi := Nat.eq_of_beq_eq_true (allL_mem hl e he)
      have h1 : codeE e = e % 33554432 := Nat.and_two_pow_sub_one_eq_mod e 25
      have h2 : Nat.land e 32767 = e % 32768 := Nat.and_two_pow_sub_one_eq_mod e 15
      have h3 : Nat.shiftRight (codeE e) 15 = codeE e / 32768 := Nat.shiftRight_eq_div_pow _ 15
      refine ⟨l, List.mem_cons.mpr (Or.inl rfl), e, he, ?_⟩
      rw [h3, h1] at hi
      rw [h2] at h'
      rw [h1]
      omega

theorem indB_inv {B : List (List Nat)} (hb : bOK B 0 = true) : CovInv B (indB B) :=
  fun c _ h => by
    obtain ⟨l, hl, e, he, h'⟩ := indB_bit hb h
    exact ⟨.var, l, hl, e, he, by simp [h', Wd.evalC]⟩

theorem msK_spec {k : List Nat → Bool} (h : msK k = true) :
    ∃ Ms : List Nat, (∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
      ∧ k Ms = true := by
  simp only [msK, frc_eq] at h
  refine ⟨_, fun j hj x => ?_, h⟩
  rw [← pln_bit j 25 x, nthL_eq]
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
theorem matOf_map {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {c : Nat} (hc : c < 2 ^ 25) : (matOf Ms).map (fun n => n.testBit c) = ofC c := by
  have hM : ∀ j, j < 25 → (nthL Ms j).testBit c = c.testBit j := fun j hj => by
    rw [hMs j hj, decide_eq_true hc, Bool.true_and]
  simp (disch := omega) only [matOf, M5.map, R5.map, hM, ofC, rowB, r0_bit, r1_bit, r2_bit,
    r3_bit, r4_bit, Nat.reduceAdd]

theorem lt16 {x : Nat} (hx : x < 32) : decide (x < 16) = !x.testBit 4 := by
  interval_cases x <;> decide

theorem stabW4_eq (c : Nat) :
    stabW4 c = !(c.testBit 4 || c.testBit 9 || c.testBit 14 || c.testBit 19) := by
  simp only [stabW4, lt16 (r0_lt c), lt16 (r1_lt c), lt16 (r2_lt c), lt16 (r3_lt c), rb0_bit,
    rb1_bit, rb2_bit, rb3_bit, decide_true, Bool.true_and]
  cases c.testBit 4 <;> cases c.testBit 9 <;> cases c.testBit 14 <;> cases c.testBit 19 <;> rfl

theorem tPlane_bit {Ms : List Nat}
    (hMs : ∀ j < 25, ∀ x, (nthL Ms j).testBit x = (decide (x < 2 ^ 25) && x.testBit j))
    {t c : Nat} (ht : t.testBit c = true) (hc : c < 2 ^ 25) :
    (tPlane Ms t).testBit c = (nonsing c && !stabW4 c) := by
  have hM : ∀ j, j < 25 → (nthL Ms j).testBit c = c.testBit j := fun j hj => by
    rw [hMs j hj, decide_eq_true hc, Bool.true_and]
  have hns : (nsK (natOps t) (matOf Ms)).testBit c = nonsing c := by
    rw [nsK_eq _ (natOps_bd t), nsD_map (natOps t) boolOps (fun n => n.testBit c)
      (fun p q => Nat.testBit_and p q c) (fun p q => Nat.testBit_or p q c)
      (fun p q => Nat.testBit_xor p q c) ht (Nat.zero_testBit c), matOf_map hMs hc,
      Bool.eq_iff_iff, nsD_ofC, nonsing_iff]
    exact ⟨fun h v h0 h1 => h v h0 (by omega), fun h v h0 h1 => h v h0 (by omega)⟩
  simp (disch := omega) only [tPlane, cv_land, cv_lor, Nat.testBit_and, Nat.testBit_or, hns, hM,
    stabW4_eq, Bool.not_not, Bool.or_assoc]

theorem allOnes_bit {X c : Nat} (hc : c < X) : (Nat.sub (Nat.shiftLeft 1 X) 1).testBit c = true := by
  have e : Nat.sub (Nat.shiftLeft 1 X) 1 = 2 ^ X - 1 := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hc

theorem cover_sound {B RO LO : List (List Nat)} (h : coverOK B RO LO = true) {c : Nat} (hc : c < N)
    (hns : nonsing c = true) (hst : stabW4 c = false) :
    ∃ τ : Wd, ∃ l ∈ B, ∃ e ∈ l, τ.evalC c = codeE e := by
  have hc' : c < 2 ^ 25 := hc
  have hcN : c < 33554432 := hc
  unfold coverOK at h
  generalize hT : Nat.sub (Nat.shiftLeft 1 33554432) 1 = t at h
  have ht : t.testBit c = true := by
    rw [← hT]
    exact allOnes_bit hcN
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hb, hops⟩, hm⟩ := h
  rw [frc_eq] at hm
  obtain ⟨Ms, hMs, hm⟩ := msK_spec hm
  simp only [frc_eq] at hm
  have hbit := congrArg (fun x => x.testBit c) (Nat.eq_of_beq_eq_true hm)
  simp only [cv_land, cv_xor, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit,
    tPlane_bit hMs ht hc', hns, hst, ht] at hbit
  simp only [opsOK, Bool.and_eq_true] at hops
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o6⟩, o7⟩, b0⟩, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩,
    b7⟩ := hops
  have hR : GoodOs (gens4 RO) := gens_ok (f := fun i => .mul .var (.gen i)) fun i hi => by
    interval_cases i
    exacts [⟨o0, basis_right b0⟩, ⟨o1, basis_right b1⟩, ⟨o2, basis_right b2⟩,
      ⟨o3, basis_right b3⟩]
  have hL : GoodOs (gens4 LO) := gens_ok (f := fun i => .mul (.gen i) .var) fun i hi => by
    interval_cases i
    exacts [⟨o4, basis_left b4⟩, ⟨o5, basis_left b5⟩, ⟨o6, basis_left b6⟩,
      ⟨o7, basis_left b7⟩]
  exact roundsS_inv hMs hL 3 (roundsS_inv hMs hR 3 (indB_inv hb)) c hc' (by simpa using hbit)

end Cover

theorem certsOK_mem {X : List Nat} :
    ∀ {B : List (List Nat)}, certsOK X B = true → ∀ l ∈ B, allL (certOK X) l = true
  | [], _, l, hl => absurd hl List.not_mem_nil
  | a :: B, h, l, hl => by
    have h' : Bool.rec (motive := fun _ => Bool) false (certsOK X B) (allL (certOK X) a) = true :=
      h
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
  have h1 := allL_mem (certsOK_mem h l hl) e he
  unfold certOK at h1
  cases hc : (Nat.blt (Nat.shiftRight e 46) 24 && Nat.blt (Nat.land (Nat.shiftRight e 36) 31) 24 &&
      Nat.blt (Nat.land (Nat.shiftRight e 25) 31) 24) <;> rw [hc] at h1
  · exact absurd h1 Bool.false_ne_true
  · simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    obtain ⟨⟨hz, h2⟩, h3⟩ := hc
    refine ⟨.mul (x0W (Nat.shiftRight e 46)) (.pow (.mul (x0W (Nat.land (Nat.shiftRight e 36) 31))
      (.pow (.mul (x0W (Nat.land (Nat.shiftRight e 25) 31)) .var)
        (Nat.land (Nat.shiftRight e 30) 63))) (Nat.land (Nat.shiftRight e 41) 31)), ?_⟩
    have h1' : goodF (mulF (nthL X (Nat.shiftRight e 46))
        (powF (mulF (nthL X (Nat.land (Nat.shiftRight e 36) 31))
          (powF (mulF (nthL X (Nat.land (Nat.shiftRight e 25) 31)) (codeE e))
            (Nat.land (Nat.shiftRight e 30) 63)))
          (Nat.land (Nat.shiftRight e 41) 31))) = true := h1
    simp only [goodF_eq, mulF_eq, powF_eq, nthL_X hX hz (codeE e), nthL_X hX h2 (codeE e),
      nthL_X hX h3 (codeE e)] at h1'
    simpa only [Wd.evalC] using h1'

end CFSG.KC.GL5B

end
