module

public import CFSG.Certificates.Kernel.BabyMonster.PktCheck
public import Certificates.Data.Kernel.BabyMonster.PktShape

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KC.YModel

theorem pkt_andB_assoc (x y z : Bool) : andB (andB x y) z = andB x (andB y z) := by
  cases x <;> cases y <;> rfl

theorem pkt_andB_eq_true {x y : Bool} : andB x y = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> simp [andB]

@[expose] noncomputable def pktAllFrom (f : Nat → Bool) (a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f (Nat.add a i))) n

theorem pkt_allFrom_zero_left (f : Nat → Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) n = pktAllFrom f 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show andB _ (f n) = andB (pktAllFrom f 0 n) (f (Nat.add 0 n))
    rw [ih, show Nat.add 0 n = n from Nat.zero_add n]

theorem pkt_allFrom_add (f : Nat → Bool) (a b c : Nat) :
    pktAllFrom f a (b + c) = andB (pktAllFrom f a b) (pktAllFrom f (a + b) c) := by
  induction c with
  | zero => cases h : pktAllFrom f a b <;> rfl
  | succ c ih =>
    show andB (pktAllFrom f a (b + c)) (f (Nat.add a (b + c))) =
      andB (pktAllFrom f a b) (andB (pktAllFrom f (a + b) c) (f (Nat.add (a + b) c)))
    rw [ih, pkt_andB_assoc, show Nat.add a (b + c) = Nat.add (a + b) c from (Nat.add_assoc a b c).symm]

@[expose] noncomputable def pktLineHead (p : Nat × Nat) (a : Nat) : Bool :=
  andB (Nat.ble a (Nat.div p.2 (nat_lit 3))) ((fun e => andB (Nat.blt (nat_lit 0) e) (andB (Nat.beq (Nat.add (Nat.mul (nat_lit 3) e) (nat_lit 1)) p.2)
    (andB (Nat.beq (chAt p.1 (Nat.mul (nat_lit 3) e)) (nat_lit 10))
      (Nat.beq (Nat.div (entV p.1 (Nat.sub e (nat_lit 1))) (nat_lit 65536)) (nat_lit 1)))))
    (Nat.div p.2 (nat_lit 3)))

@[expose] noncomputable def pktEntsOK (p : Nat × Nat) (a n : Nat) : Bool :=
  pktAllFrom (fun i => Nat.blt (entV p.1 i) (nat_lit 262144)) a n

@[expose] noncomputable def pktEntsTail (p : Nat × Nat) (a : Nat) : Bool :=
  pktEntsOK p a (Nat.sub (Nat.div p.2 (nat_lit 3)) a)

theorem pkt_lineOK_split (p : Nat × Nat) (a : Nat)
    (h0 : pktLineHead p a = true) (h1 : pktEntsOK p 0 a = true)
    (h2 : pktEntsTail p a = true) : lineOK p = true := by
  unfold pktLineHead at h0
  obtain ⟨ha, h0⟩ := pkt_andB_eq_true.1 h0
  unfold pktEntsTail pktEntsOK at h2
  unfold pktEntsOK at h1
  unfold lineOK
  generalize Nat.div p.2 (nat_lit 3) = e at h0 h2 ha
  have ha' : a ≤ e := Nat.le_of_ble_eq_true ha
  obtain ⟨g1, h0⟩ := pkt_andB_eq_true.1 h0
  obtain ⟨g2, h0⟩ := pkt_andB_eq_true.1 h0
  obtain ⟨g3, g4⟩ := pkt_andB_eq_true.1 h0
  simp only [g1, g2, g3, g4, pkt_andB_eq_true, true_and]
  rw [pkt_allFrom_zero_left, show e = a + (e - a) by omega, pkt_allFrom_add, pkt_andB_eq_true]
  refine ⟨h1, ?_⟩
  rw [Nat.zero_add]
  exact h2

@[expose] noncomputable def pktShapeRun (N : Nat) (s : Nat × Nat × Bool) (a n : Nat) : Nat × Nat × Bool :=
  Nat.rec (motive := fun _ => Nat × Nat × Bool) s (fun i ih => shStep ih (entV N (Nat.add a i))) n

theorem pkt_shapeRun_zero_left (N : Nat) (s : Nat × Nat × Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Nat × Nat × Bool) s (fun i ih => shStep ih (entV N i)) n =
      pktShapeRun N s 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show shStep _ (entV N n) = shStep (pktShapeRun N s 0 n) (entV N (Nat.add 0 n))
    rw [ih, show Nat.add 0 n = n from Nat.zero_add n]

theorem pkt_shapeRun_add (N : Nat) (s : Nat × Nat × Bool) (a b c : Nat) :
    pktShapeRun N s a (b + c) = pktShapeRun N (pktShapeRun N s a b) (a + b) c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show shStep (pktShapeRun N s a (b + c)) (entV N (Nat.add a (b + c))) =
      shStep (pktShapeRun N (pktShapeRun N s a b) (a + b) c) (entV N (Nat.add (a + b) c))
    rw [ih, show Nat.add a (b + c) = Nat.add (a + b) c from (Nat.add_assoc a b c).symm]

@[expose] noncomputable def pktShapeHead (p : Nat × Nat) (a : Nat) (s : Nat × Nat × Bool) : Bool :=
  andB (Nat.ble a (Nat.div p.2 (nat_lit 3)))
    ((fun t => andB (Nat.beq t.1 s.1) (andB (Nat.beq t.2.1 s.2.1)
        (Bool.rec (motive := fun _ => Bool) (notB s.2.2) s.2.2 t.2.2)))
      (pktShapeRun p.1 (nat_lit 0, nat_lit 0, true) 0 a))

@[expose] noncomputable def pktShapeTail (p : Nat × Nat) (a : Nat) (s : Nat × Nat × Bool) : Bool :=
  (fun st => andB (Nat.beq st.1 (nat_lit 4371)) st.2.2)
    (pktShapeRun p.1 s a (Nat.sub (Nat.div p.2 (nat_lit 3)) a))

theorem pkt_shapeOK_split (p : Nat × Nat) (a : Nat) (s : Nat × Nat × Bool)
    (h1 : pktShapeHead p a s = true) (h2 : pktShapeTail p a s = true) : shapeOK p = true := by
  unfold pktShapeHead at h1
  obtain ⟨ha, h1⟩ := pkt_andB_eq_true.1 h1
  simp only at h1
  obtain ⟨e1, h1⟩ := pkt_andB_eq_true.1 h1
  obtain ⟨e2, e3⟩ := pkt_andB_eq_true.1 h1
  have hs : pktShapeRun p.1 (nat_lit 0, nat_lit 0, true) 0 a = s := by
    obtain ⟨s1, s2, s3⟩ := s
    generalize pktShapeRun p.1 (nat_lit 0, nat_lit 0, true) 0 a = t at e1 e2 e3
    obtain ⟨t1, t2, t3⟩ := t
    have := Nat.eq_of_beq_eq_true e1
    have := Nat.eq_of_beq_eq_true e2
    cases t3 <;> cases s3 <;> simp_all [notB]
  unfold shapeOK
  unfold pktShapeTail at h2
  rw [pkt_shapeRun_zero_left]
  generalize Nat.div p.2 (nat_lit 3) = e at h2 ha ⊢
  have ha' : a ≤ e := Nat.le_of_ble_eq_true ha
  rw [show e = a + (e - a) by omega, pkt_shapeRun_add, hs, Nat.zero_add]
  exact h2

@[expose] noncomputable def pktSparseRest (p : Nat × Nat) (SG : List (List Nat)) : Bool :=
  andB (Nat.ble p.2 (nat_lit 786432))
    ((fun e => (fun st => andB (Nat.beq st.1 (nat_lit 4371)) (Nat.beq st.2 (nat_lit 0)))
      (List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ st => st)
        (fun N _ ih m st => (fun c => (fun st' => forceP st'.1 (ih (Nat.sub m c) st'))
            (sparseRun SG N 0 c st))
          (Nat.min m (nat_lit 64)))
        (splitN (nat_lit 192) (nat_lit 12) p.1) e (nat_lit 0, nat_lit 0)))
      (Nat.div p.2 (nat_lit 3)))

theorem pkt_sparseOK_of (p : Nat × Nat) (SG : List (List Nat)) (h1 : lineOK p = true)
    (h2 : pktSparseRest p SG = true) : sparseOK p SG = true := by
  unfold sparseOK
  rw [h1]
  exact h2

end CFSG.KC.BM.Pkt

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KC.YModel

theorem pkt_lineOK_split3 (p : Nat × Nat) (a b : Nat) (hab : a ≤ b)
    (h0 : pktLineHead p b = true) (h1 : pktEntsOK p 0 a = true) (h2 : pktEntsOK p a (b - a) = true)
    (h3 : pktEntsTail p b = true) : lineOK p = true := by
  refine pkt_lineOK_split p b h0 ?_ h3
  unfold pktEntsOK at h1 h2 ⊢
  rw [show b = a + (b - a) by omega, pkt_allFrom_add, pkt_andB_eq_true, Nat.zero_add]
  exact ⟨h1, h2⟩

@[expose] noncomputable def pktShapeMid (p : Nat × Nat) (a b : Nat) (s t : Nat × Nat × Bool) : Bool :=
  andB (Nat.ble b (Nat.div p.2 (nat_lit 3)))
    ((fun u => andB (Nat.beq u.1 t.1) (andB (Nat.beq u.2.1 t.2.1)
        (Bool.rec (motive := fun _ => Bool) (notB t.2.2) t.2.2 u.2.2)))
      (pktShapeRun p.1 s a (Nat.sub b a)))

theorem pkt_stEq {u t : Nat × Nat × Bool}
    (h : andB (Nat.beq u.1 t.1) (andB (Nat.beq u.2.1 t.2.1)
      (Bool.rec (motive := fun _ => Bool) (notB t.2.2) t.2.2 u.2.2)) = true) : u = t := by
  obtain ⟨u1, u2, u3⟩ := u
  obtain ⟨t1, t2, t3⟩ := t
  obtain ⟨e1, h⟩ := pkt_andB_eq_true.1 h
  obtain ⟨e2, e3⟩ := pkt_andB_eq_true.1 h
  have := Nat.eq_of_beq_eq_true e1
  have := Nat.eq_of_beq_eq_true e2
  cases u3 <;> cases t3 <;> simp_all [notB]

theorem pkt_shapeOK_split3 (p : Nat × Nat) (a b : Nat) (hab : a ≤ b) (s t : Nat × Nat × Bool)
    (h1 : pktShapeHead p a s = true) (h2 : pktShapeMid p a b s t = true)
    (h3 : pktShapeTail p b t = true) : shapeOK p = true := by
  unfold pktShapeHead at h1
  obtain ⟨_, h1⟩ := pkt_andB_eq_true.1 h1
  have hs := pkt_stEq h1
  unfold pktShapeMid at h2
  obtain ⟨hb, h2⟩ := pkt_andB_eq_true.1 h2
  have ht := pkt_stEq h2
  have hrun : pktShapeRun p.1 (nat_lit 0, nat_lit 0, true) 0 b = t := by
    rw [show b = a + (b - a) by omega, pkt_shapeRun_add, hs, Nat.zero_add]
    exact ht
  refine pkt_shapeOK_split p b t ?_ h3
  unfold pktShapeHead
  rw [hb, hrun]
  obtain ⟨t1, t2, t3⟩ := t
  cases t3 <;> simp [andB, notB, Nat.beq_refl]

end CFSG.KC.BM.Pkt

end
