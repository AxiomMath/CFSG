module

public import Certificates.Data.Kernel.Ssa3

public section

namespace CFSG.KC.Ssa3Split

open CFSG.KC.Loop CFSG.KC.Ssa3

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] def eqLN : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && eqLN as bs
  | _, _ => false

theorem eq_of_eqLN : ∀ {L M : List Nat}, eqLN L M = true → L = M
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [eqLN, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eq_of_eqLN h.2]
  | [], _ :: _, h => by simp [eqLN] at h
  | _ :: _, [], h => by simp [eqLN] at h

@[expose] def okC (D : SData) (lo j : Nat) : Bool :=
  (Nat.ble (3 + lo) (D.na.getD j 0) || availS D lo (D.na.getD j 0)) &&
    (!Nat.beq (D.nk.getD j 1) 0 || Nat.ble (3 + lo) (D.nb.getD j 0) ||
      availS D lo (D.nb.getD j 0))

@[expose] noncomputable def nodeV (R : Ar) (D : SData) (lo : Nat) (L : List Nat) (j : Nat) : Nat :=
  bif Nat.beq (D.nk.getD j 1) 0 then
    R.mul (getV R D lo L (D.na.getD j 0)) (getV R D lo L (D.nb.getD j 0))
  else powT R.mul R.one (getV R D lo L (D.na.getD j 0)) (D.nk.getD j 1)

@[expose] noncomputable def okS (R : Ar) (D : SData) (j v : Nat) : Bool :=
  Nat.beq (D.ns.getD j 0) 0 || Nat.beq v (R.mt (Nat.sub (D.ns.getD j 0) 1))

@[expose] noncomputable def stepV (R : Ar) (D : SData) (lo j : Nat) (L : List Nat) (v : Nat)
    (k : Nat → List Nat → Nat) : Nat :=
  bif okC D lo j then (bif okS R D j v then k (j + 1) (L ++ [v]) else 0) else 0

theorem runC_succ (R : Ar) (D : SData) (lo : Nat) (fin : List Nat → Nat) (m j : Nat)
    (L : List Nat) :
    runC R D lo fin (m + 1) j L = stepV R D lo j L (nodeV R D lo L j) (runC R D lo fin m) := by
  show (bif okC D lo j then strictN (nodeV R D lo L j) (fun v =>
      bif okS R D j v then runC R D lo fin m (j + 1) (L ++ [v]) else 0) else 0) = _
  rw [strictN_eq]; rfl

theorem stepV_congr {R : Ar} {D : SData} {lo j : Nat} {L : List Nat} {v : Nat}
    {k k' : Nat → List Nat → Nat} (h : ∀ L', k (j + 1) L' = k' (j + 1) L') :
    stepV R D lo j L v k = stepV R D lo j L v k' := by
  simp only [stepV, h]

theorem runC_add (R : Ar) (D : SData) (lo : Nat) (fin : List Nat → Nat) (m2 : Nat) :
    ∀ (m1 j : Nat) (L : List Nat), runC R D lo fin (m2 + m1) j L =
      runC R D lo (fun L' => runC R D lo fin m2 (j + m1) L') m1 j L
  | 0, j, L => rfl
  | m1 + 1, j, L => by
    rw [← Nat.add_assoc, runC_succ, runC_succ]
    refine stepV_congr fun L' => ?_
    rw [runC_add R D lo fin m2 m1 (j + 1) L', Nat.add_right_comm, Nat.add_assoc]

@[expose] noncomputable def ckL (Lr L : List Nat) : Nat := bif eqLN L Lr then 1 else 0

theorem stepV_eq_one {R : Ar} {D : SData} {lo j : Nat} {L : List Nat} {v : Nat}
    {k : Nat → List Nat → Nat} (h : stepV R D lo j L v k = 1) :
    okC D lo j = true ∧ okS R D j v = true ∧ k (j + 1) (L ++ [v]) = 1 := by
  unfold stepV at h
  cases hc : okC D lo j <;> cases hs : okS R D j v <;> simp_all

theorem stepV_of {R : Ar} {D : SData} {lo j : Nat} {L : List Nat} {v : Nat}
    {k : Nat → List Nat → Nat} (hc : okC D lo j = true) (hs : okS R D j v = true) :
    stepV R D lo j L v k = k (j + 1) (L ++ [v]) := by
  simp only [stepV, hc, hs, Bool.cond_true]

theorem runC_ck {R : Ar} {D : SData} {lo : Nat} {Lr : List Nat} :
    ∀ {m j : Nat} {L : List Nat}, runC R D lo (ckL Lr) m j L = 1 →
      ∀ f, runC R D lo f m j L = f Lr
  | 0, j, L, h, f => by
    have h' : ckL Lr L = 1 := h
    unfold ckL at h'
    cases he : eqLN L Lr
    · simp [he] at h'
    · exact congrArg f (eq_of_eqLN he)
  | m + 1, j, L, h, f => by
    rw [runC_succ] at h ⊢
    obtain ⟨hc, hs, hk⟩ := stepV_eq_one h
    rw [stepV_of hc hs]
    exact runC_ck hk f

theorem runC_seq {R : Ar} {D : SData} {lo m1 j : Nat} {L Lr : List Nat}
    (h : Nat.beq (runC R D lo (ckL Lr) m1 j L) 1 = true) {f : List Nat → Nat} {m m2 j2 : Nat}
    (hm : m = m2 + m1) (hj : j2 = j + m1) :
    runC R D lo f m j L = runC R D lo f m2 j2 Lr := by
  subst hm hj
  rw [runC_add]
  exact runC_ck (Nat.eq_of_beq_eq_true h) _

theorem runC_node {R : Ar} {D : SData} {lo j : Nat} {L : List Nat} {v : Nat}
    (hv : nodeV R D lo L j = v) (h : (okC D lo j && okS R D j v) = true) {f : List Nat → Nat}
    {m m2 j2 : Nat} {Lr : List Nat} (hm : m = m2 + 1) (hj : j2 = j + 1) (hL : L ++ [v] = Lr) :
    runC R D lo f m j L = runC R D lo f m2 j2 Lr := by
  subst hm hj hL
  rw [runC_succ, hv]
  simp only [Bool.and_eq_true] at h
  exact stepV_of h.1 h.2

theorem nodeV_pow {R : Ar} {D : SData} {lo : Nat} {L : List Nat} {j : Nat}
    (h : Nat.beq (D.nk.getD j 1) 0 = false) :
    nodeV R D lo L j = powT R.mul R.one (getV R D lo L (D.na.getD j 0)) (D.nk.getD j 1) := by
  simp only [nodeV, h, Bool.cond_false]

@[expose] noncomputable def powS (mul : Nat → Nat → Nat) (X e i : Nat) (ih : Nat → Bool → Nat)
    (acc : Nat) (st : Bool) : Nat :=
  bif st then
    strictN (mul acc acc) fun s =>
      bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then strictN (mul s X) fun t => ih t true
      else ih s true
  else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ih X true else ih acc false

@[expose] noncomputable def powR (mul : Nat → Nat → Nat) (one X e n : Nat) : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Nat → Bool → Nat) (fun acc st => bif st then acc else one)
    (fun i ih => powS mul X e i ih) n

@[expose] noncomputable def powTop (mul : Nat → Nat → Nat) (X e k : Nat) (C : Nat → Bool → Nat)
    (t : Nat) : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Nat → Bool → Nat) C (fun i ih => powS mul X e (k + i) ih) t

theorem powT_gen (mul : Nat → Nat → Nat) (one X e : Nat) : ∀ n,
    (Nat.rec (motive := fun _ => Nat → Bool → Nat) (fun acc st => bif st then acc else one)
      (fun i ih acc st =>
        bif st then
          strictN (mul acc acc) fun s =>
            bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then strictN (mul s X) fun t => ih t true
            else ih s true
        else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ih X true else ih acc false)
      n : Nat → Bool → Nat) = powR mul one X e n
  | 0 => rfl
  | n + 1 => by
    show powS mul X e n (Nat.rec (motive := fun _ => Nat → Bool → Nat)
      (fun acc st => bif st then acc else one)
      (fun i ih acc st =>
        bif st then
          strictN (mul acc acc) fun s =>
            bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then strictN (mul s X) fun t => ih t true
            else ih s true
        else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ih X true else ih acc false)
      n) = powS mul X e n (powR mul one X e n)
    rw [powT_gen mul one X e n]

theorem powT_eq (mul : Nat → Nat → Nat) (one X e : Nat) :
    powT mul one X e = powR mul one X e 16 one false :=
  congrFun (congrFun (powT_gen mul one X e 16) one) false

theorem powR_add (mul : Nat → Nat → Nat) (one X e k : Nat) :
    ∀ t, powR mul one X e (k + t) = powTop mul X e k (powR mul one X e k) t
  | 0 => rfl
  | t + 1 => by
    show powS mul X e (k + t) (powR mul one X e (k + t)) = powS mul X e (k + t) _
    rw [powR_add mul one X e k t]
    rfl

@[expose] noncomputable def ckP (A acc : Nat) (st : Bool) : Nat := bif st && Nat.beq acc A then 1 else 0

theorem powTop_ck {mul : Nat → Nat → Nat} {X e k A : Nat} :
    ∀ {t acc st}, powTop mul X e k (ckP A) t acc st = 1 →
      ∀ C, powTop mul X e k C t acc st = C A true
  | 0, acc, st, h, C => by
    have h' : ckP A acc st = 1 := h
    unfold ckP at h'
    cases st
    · simp at h'
    · cases hb : Nat.beq acc A
      · simp [hb] at h'
      · rw [Nat.eq_of_beq_eq_true hb]; rfl
  | t + 1, acc, st, h, C => by
    change powS mul X e (k + t) (powTop mul X e k (ckP A) t) acc st = 1 at h
    show powS mul X e (k + t) (powTop mul X e k C t) acc st = _
    unfold powS at h ⊢
    simp only [strictN_eq] at h ⊢
    cases st <;> cases hb : Nat.beq (Nat.land (Nat.shiftRight e (k + t)) 1) 1 <;>
      simp only [hb, Bool.cond_true, Bool.cond_false] at h ⊢ <;> exact powTop_ck h C

theorem powR_seq {mul : Nat → Nat → Nat} {one X e k t acc : Nat} {st : Bool} {A : Nat}
    (h : Nat.beq (powTop mul X e k (ckP A) t acc st) 1 = true) {n : Nat} (hn : n = k + t) :
    powR mul one X e n acc st = powR mul one X e k A true := by
  subst hn
  rw [powR_add]
  exact powTop_ck (Nat.eq_of_beq_eq_true h) _

theorem powR_last {mul : Nat → Nat → Nat} {one X e k acc v : Nat} {st : Bool}
    (h : Nat.beq (powR mul one X e k acc st) v = true) : powR mul one X e k acc st = v :=
  Nat.eq_of_beq_eq_true h

@[expose] noncomputable def finC (R : Ar) (D : SData) (c lo hi : Nat) (L : List Nat) : Nat :=
  bif (List.range' (D.qb.getD c 0) (D.qb.getD (c + 1) 0 - D.qb.getD c 0)).all
    (cmpOK R D lo hi L) then 1 else 0

theorem chunkOK_eq {R : Ar} {D : SData} {c lo hi m : Nat} (hlo : D.cb.getD c 0 = lo)
    (hhi : D.cb.getD (c + 1) 0 = hi) (hm : hi - lo = m) :
    chunkOK R D c = Nat.beq (runC R D lo (finC R D c lo hi) m lo []) 1 := by
  subst hlo hhi hm; rfl

end CFSG.KC.Ssa3Split

end
