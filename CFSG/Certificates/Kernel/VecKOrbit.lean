module

public import Certificates.Data.Kernel.VecK
public import Certificates.Data.CFSGNative.HS.Cert
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Certificates.Kernel.PosTableSound
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native

abbrev VSt := Array UInt32 × Array Nat × Table × Table

@[expose] def vIns {β : Type} (d : Nat) (c : Array Nat) (v : Nat) (pos : Array UInt32)
    (pts : Array Nat) (k : Array UInt32 → Array Nat → β) : β :=
  if (pos[vecMulN d c v]! == none32) = true then
    k (pos.set! (vecMulN d c v) (UInt32.ofNat pts.size)) (pts.push (vecMulN d c v))
  else k pos pts

@[expose] def vBody (d : Nat) (cA cB : Array Nat) (h : Nat) (s : VSt) : Id (ForInStep VSt) :=
  if h < s.2.1.size then
    vIns d cA s.2.1[h]! s.1 s.2.1 fun pos pts =>
      vIns d cB s.2.1[h]! pos pts fun pos' pts' =>
        pure (.yield (pos', pts', s.2.2.1.push pos[vecMulN d cA s.2.1[h]!]!,
          s.2.2.2.push pos'[vecMulN d cB s.2.1[h]!]!))
  else pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

theorem vOrbitBFS_eq (d : Nat) (cA cB : Array Nat) (v0 cap : Nat) :
    vOrbitBFS d cA cB v0 cap =
      ⟨(forIn [0:cap] ((Array.replicate (1 <<< d) none32).set! v0 0, #[v0], #[], #[])
          (vBody d cA cB) : Id VSt).2.1,
        (forIn [0:cap] ((Array.replicate (1 <<< d) none32).set! v0 0, #[v0], #[], #[])
          (vBody d cA cB) : Id VSt).2.2.1,
        (forIn [0:cap] ((Array.replicate (1 <<< d) none32).set! v0 0, #[v0], #[], #[])
          (vBody d cA cB) : Id VSt).2.2.2⟩ := rfl

theorem vIns_eq {β : Type} (d : Nat) (c : Array Nat) (v : Nat) (pos : Array UInt32)
    (pts : Array Nat) (k : Array UInt32 → Array Nat → β) :
    vIns d c v pos pts k =
      k (if (pos[vecMulN d c v]! == none32) = true then
          pos.set! (vecMulN d c v) (UInt32.ofNat pts.size) else pos)
        (if (pos[vecMulN d c v]! == none32) = true then pts.push (vecMulN d c v) else pts) := by
  unfold vIns
  split <;> rfl

private theorem forIn_inv {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_inv R E f hf k (a + 1) b' (by omega) hR

structure OInv (n d : Nat) (p fo : Nat → Nat) (k m : Nat) (pos : Array UInt32) (pts : Array Nat) :
    Prop where
  pts_eq : pts = ((List.range m).map p).toArray
  m_pos : 1 ≤ m
  m_le : m ≤ n
  disc : ∀ y, 1 ≤ y → y < n → (y < m ↔ fo y < k)
  size : pos.size = 2 ^ d
  hit : ∀ y < m, pos[p y]! = UInt32.ofNat y
  miss : ∀ v < 2 ^ d, (∀ y < m, p y ≠ v) → pos[v]! = none32

private theorem ofNat_ne_none {x : Nat} (hx : x < 2 ^ 30) : UInt32.ofNat x ≠ none32 := by
  intro e
  have h := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  omega

private theorem toArray_get {p : Nat → Nat} {m y : Nat} (hy : y < m) :
    ((List.range m).map p).toArray[y]! = p y := by
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

private theorem toArray_size (p : Nat → Nat) (m : Nat) : ((List.range m).map p).toArray.size = m := by
  simp

private theorem push_range (p : Nat → Nat) (m : Nat) :
    (((List.range m).map p).toArray).push (p m) = ((List.range (m + 1)).map p).toArray := by
  rw [List.range_succ, List.map_append]
  simp

theorem fo_mono {n : Nat} {fo : Nat → Nat} (h : ∀ y, 1 ≤ y → y + 1 < n → fo y < fo (y + 1)) :
    ∀ y z, 1 ≤ y → y < z → z < n → fo y < fo z := by
  intro y z hy hyz hz
  induction z with
  | zero => omega
  | succ z ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hyz with h1 | h1
    · exact (ih h1 (by omega)).trans (h z (by omega) hz)
    · subst h1
      exact h y hy hz

theorem ins_step {n d k m : Nat} {p fo : Nat → Nat} {pos : Array UInt32} {pts : Array Nat} {x : Nat}
    (hn : n < 2 ^ 30) (hlt : ∀ h < n, p h < 2 ^ d) (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hmono : ∀ y z, 1 ≤ y → y < z → z < n → fo y < fo z)
    (H : OInv n d p fo k m pos pts) (hx : x < n)
    (hnew : ∀ y, 1 ≤ y → y < n → fo y = k → y = x) (hrd : x = 0 ∨ fo x ≤ k) :
    ∃ m', OInv n d p fo (k + 1) m'
        (if (pos[p x]! == none32) = true then pos.set! (p x) (UInt32.ofNat pts.size) else pos)
        (if (pos[p x]! == none32) = true then pts.push (p x) else pts) ∧
      (if (pos[p x]! == none32) = true then pos.set! (p x) (UInt32.ofNat pts.size) else pos)[p x]! =
        UInt32.ofNat x := by
  have hsz : pts.size = m := by rw [H.pts_eq, toArray_size]
  by_cases hc : x < m
  · have hget := H.hit x hc
    have hne : (pos[p x]! == none32) = false := by
      rw [hget]
      exact beq_false_of_ne (ofNat_ne_none (by omega))
    rw [hne]
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨m, ⟨H.pts_eq, H.m_pos, H.m_le, fun y hy1 hyn => ?_, H.size, H.hit, H.miss⟩, hget⟩
    rw [H.disc y hy1 hyn]
    constructor
    · intro h
      omega
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
      · exact h1
      · have := hnew y hy1 hyn h1
        subst this
        exact absurd ((H.disc y hy1 hyn).1 hc) (by omega)
  · have hx0 : x ≠ 0 := by have := H.m_pos; omega
    have hfx : fo x = k := by
      rcases hrd with h | h
      · exact absurd h hx0
      · have := (H.disc x (by omega) hx).not.1 hc
        omega
    have hxm : x = m := by
      by_contra hne
      have hmx : m < x := by omega
      have h1 := hmono m x H.m_pos hmx hx
      have h2 := (H.disc m H.m_pos (by omega)).not.1 (Nat.lt_irrefl m)
      omega
    subst hxm
    have hmiss : pos[p x]! = none32 :=
      H.miss (p x) (hlt x hx) fun y hy e => by
        have := hinj y (by omega) x hx e
        omega
    have hcond : (pos[p x]! == none32) = true := by rw [hmiss]; exact beq_self_eq_true _
    rw [hcond]
    simp only [ite_true]
    have hself : (pos.set! (p x) (UInt32.ofNat pts.size))[p x]! = UInt32.ofNat x := by
      rw [Array.getElem!_set!_self _ _ _ (by rw [H.size]; exact hlt x hx), hsz]
    refine ⟨x + 1, ⟨?_, by omega, by omega, fun y hy1 hyn => ?_, by rw [Array.size_set!, H.size],
      fun y hy => ?_, fun v hv hall => ?_⟩, hself⟩
    · rw [H.pts_eq, push_range]
    · constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
        · have := (H.disc y hy1 hyn).1 h1
          omega
        · subst h1
          omega
      · intro h
        by_contra hge
        have := hmono x y (by omega) (by omega) hyn
        omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h1 | h1
      · have hne : p x ≠ p y := fun e => by
          have := hinj x hx y (by omega) e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ hne]
        exact H.hit y h1
      · subst h1
        exact hself
    · have hne : p x ≠ v := hall x (Nat.lt_succ_self x)
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact H.miss v hv fun y hy => hall y (by omega)

theorem vOrbitBFS_sim {d n : Nat} {cA cB : Array Nat} {p a b fo sq : Nat → Nat}
    (hn0 : 0 < n) (hn : n < 2 ^ 30) (hlt : ∀ h < n, p h < 2 ^ d)
    (ha : ∀ h < n, a h < n) (hb : ∀ h < n, b h < n)
    (hA : ∀ h < n, vecMulN d cA (p h) = p (a h)) (hB : ∀ h < n, vecMulN d cB (p h) = p (b h))
    (hinj : ∀ i < n, ∀ j < n, p i = p j → i = j)
    (hsqA : ∀ h, sq (2 * h) = a h) (hsqB : ∀ h, sq (2 * h + 1) = b h)
    (hfo : ∀ y, 1 ≤ y → y < n → fo y < 2 * y ∧ sq (fo y) = y)
    (hfo1 : ∀ y, 1 ≤ y → y + 1 < n → fo y < fo (y + 1))
    (hrdA : ∀ h < n, a h = 0 ∨ fo (a h) ≤ 2 * h) (hrdB : ∀ h < n, b h = 0 ∨ fo (b h) ≤ 2 * h + 1) :
    vOrbitBFS d cA cB (p 0) n =
      ⟨((List.range n).map p).toArray, ((List.range n).map fun h => UInt32.ofNat (a h)).toArray,
        ((List.range n).map fun h => UInt32.ofNat (b h)).toArray⟩ := by
  have hmono := fo_mono hfo1
  let R : Nat → VSt → Prop := fun h s => ∃ m, OInv n d p fo (2 * h) m s.1 s.2.1 ∧
    s.2.2.1 = ((List.range h).map fun h => UInt32.ofNat (a h)).toArray ∧
    s.2.2.2 = ((List.range h).map fun h => UInt32.ofNat (b h)).toArray
  have hstep : ∀ j s, j < n → R j s → ∃ s', vBody d cA cB j s = pure (.yield s') ∧ R (j + 1) s' := by
    rintro j ⟨pos, pts, al, be⟩ hj ⟨m, H, hal, hbe⟩
    dsimp only at H hal hbe
    have hsz : pts.size = m := by rw [H.pts_eq, toArray_size]
    have hjm : j < m := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · have := H.m_pos
        omega
      · exact (H.disc j h0 hj).2 (by have := (hfo j h0 hj).1; omega)
    have hv : pts[j]! = p j := by rw [H.pts_eq, toArray_get hjm]
    have hjlt : j < pts.size := by omega
    unfold vBody
    simp only [hjlt, ite_true, hv, hA j hj, hB j hj, vIns_eq]
    obtain ⟨m1, H1, h1⟩ := ins_step (x := a j) hn hlt hinj hmono H (ha j hj)
      (fun y hy1 hyn e => by have := (hfo y hy1 hyn).2; rw [e, hsqA] at this; exact this.symm)
      (hrdA j hj)
    obtain ⟨m2, H2, h2⟩ := ins_step (x := b j) hn hlt hinj hmono H1 (hb j hj)
      (fun y hy1 hyn e => by have := (hfo y hy1 hyn).2; rw [e, hsqB] at this; exact this.symm)
      (hrdB j hj)
    refine ⟨_, rfl, m2, ?_, ?_, ?_⟩
    · have e : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [e]
      exact H2
    · dsimp only
      rw [h1, hal, List.range_succ, List.map_append]
      simp
    · dsimp only
      rw [h2, hbe, List.range_succ, List.map_append]
      simp
  have hinit : R 0 ((Array.replicate (1 <<< d) none32).set! (p 0) 0, #[p 0], #[], #[]) := by
    have hrs : (Array.replicate (1 <<< d) (none32 ())).size = 2 ^ d := by
      rw [Array.size_replicate, Nat.one_shiftLeft]
    refine ⟨1, ⟨by simp, le_refl 1, hn0, fun y hy1 _ => by omega, by rw [Array.size_set!, hrs],
      fun y hy => ?_, fun v hv hall => ?_⟩, by simp, by simp⟩
    · have : y = 0 := by omega
      subst this
      rw [Array.getElem!_set!_self _ _ _ (by rw [hrs]; exact hlt 0 hn0)]
      rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ (hall 0 (Nat.zero_lt_one)),
        getElem!_pos _ v (by rw [hrs]; exact hv)]
      simp
  have hend := forIn_inv R n (vBody d cA cB) hstep n 0 _ (by omega) hinit
  rw [Nat.zero_add] at hend
  rw [vOrbitBFS_eq, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  simp only [hr]
  obtain ⟨m, H, hal, hbe⟩ := hend
  have hmn : m = n := by
    by_contra hne
    have hlt' : m < n := by have := H.m_le; omega
    have h1 := (H.disc m H.m_pos hlt').not.1 (Nat.lt_irrefl m)
    have h2 := (hfo m H.m_pos hlt').1
    omega
  rw [hmn] at H
  change VOrbit.mk _ _ _ = _
  rw [← H.pts_eq, ← hal, ← hbe]

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

private theorem pw2_eq' (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

theorem cols_eq {d M N : Nat} {cs : List Char} (hb : m1Bind cs d M = true)
    (ht : Nat.beq (trK d M) N = true) :
    transposeRows d (rowsOfPayload d (String.ofList cs)) = unpackR d N := by
  rw [bind_sound hb, tr_sound ht]

theorem colsAB_eq (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true) :
    (∀ v, vecMulN D.d D.colsA v = vmF D.d NA v) ∧ ∀ v, vecMulN D.d D.colsB v = vmF D.d NB v := by
  unfold seedK at hseed
  simp only [andB_eq, Bool.and_eq_true] at hseed
  obtain ⟨-, -, -, -, hbA, hbB, htA, htB, -, -⟩ := hseed
  have eA : D.colsA = unpackR D.d NA := by
    change transposeRows D.d (rowsOfPayload D.d D.seedA) = _
    rw [hA, cols_eq hbA htA]
  have eB : D.colsB = unpackR D.d NB := by
    change transposeRows D.d (rowsOfPayload D.d D.seedB) = _
    rw [hB, cols_eq hbB htB]
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [eA, CFSG.KC.F2W.vecMulN_unpackR]
  · rw [eB, CFSG.KC.F2W.vecMulN_unpackR]

theorem orbAt_iff {d n NA NB : Nat} {P AT BT : Nat → Nat} {h : Nat} :
    orbAt d n NA NB P AT BT h = true ↔ lk P 32 h < 2 ^ d ∧ lk AT 32 h < n ∧ lk BT 32 h < n ∧
      lk P 32 (lk AT 32 h) = vmF d NA (lk P 32 h) ∧ lk P 32 (lk BT 32 h) = vmF d NB (lk P 32 h) := by
  unfold orbAt
  simp only [strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, pw2_eq']

theorem seqAt_even (AT BT : Nat → Nat) (h : Nat) : seqAt AT BT (2 * h) = lk AT 32 h := by
  unfold seqAt
  have e1 : Nat.land (2 * h) 1 = 0 := by
    change (2 * h) &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega
  have e2 : Nat.shiftRight (2 * h) 1 = h := by
    change (2 * h) >>> 1 = h
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]
  rfl

theorem seqAt_odd (AT BT : Nat → Nat) (h : Nat) : seqAt AT BT (2 * h + 1) = lk BT 32 h := by
  unfold seqAt
  have e1 : Nat.land (2 * h + 1) 1 = 1 := by
    change (2 * h + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]
    omega
  have e2 : Nat.shiftRight (2 * h + 1) 1 = h := by
    change (2 * h + 1) >>> 1 = h
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]
  rfl

theorem bfsAt_iff {n : Nat} {AT BT FO : Nat → Nat} {h : Nat} :
    bfsAt n AT BT FO h = true ↔
      (h = 0 ∨ (lk FO 32 h < 2 * h ∧ seqAt AT BT (lk FO 32 h) = h ∧
        (n ≤ h + 1 ∨ lk FO 32 h < lk FO 32 (h + 1)))) ∧
      (lk AT 32 h = 0 ∨ lk FO 32 (lk AT 32 h) ≤ 2 * h) ∧
      (lk BT 32 h = 0 ∨ lk FO 32 (lk BT 32 h) ≤ 2 * h + 1) := by
  unfold bfsAt
  simp only [strictB_eq, andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq, Nat.mul_eq, Nat.succ_eq_add_one]

theorem sortAt_iff {n : Nat} {P S IP SP : Nat → Nat} {h : Nat} :
    sortAt n P S IP SP h = true ↔ lk IP 32 h < n ∧ lk S 32 (lk IP 32 h) = lk P 32 h ∧
      lk SP 32 (lk IP 32 h) = h ∧ (n ≤ h + 1 ∨ lk S 32 h < lk S 32 (h + 1)) := by
  unfold sortAt
  simp only [strictB_eq, andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq, Nat.succ_eq_add_one]

theorem P_inj_of_sort {n : Nat} {P S IP SP : Nat → Nat} (hsort : ∀ h < n, sortAt n P S IP SP h = true) :
    ∀ i < n, ∀ j < n, lk P 32 i = lk P 32 j → i = j := by
  have hS : ∀ x y, x < y → y < n → lk S 32 x < lk S 32 y := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      have hy' := (sortAt_iff.1 (hsort y (by omega))).2.2.2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h1 | h1
      · rcases hy' with h2 | h2
        · omega
        · exact (ih h1 (by omega)).trans h2
      · subst h1
        rcases hy' with h2 | h2
        · omega
        · exact h2
  intro i hi j hj e
  obtain ⟨hi1, hi2, hi3, -⟩ := sortAt_iff.1 (hsort i hi)
  obtain ⟨hj1, hj2, hj3, -⟩ := sortAt_iff.1 (hsort j hj)
  have hk : lk IP 32 i = lk IP 32 j := by
    rcases Nat.lt_trichotomy (lk IP 32 i) (lk IP 32 j) with h1 | h1 | h1
    · have := hS _ _ h1 hj1
      omega
    · exact h1
    · have := hS _ _ h1 hi1
      omega
  rw [← hi3, ← hj3, hk]

theorem orbit_eq (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) :
    D.orbit () =
      ⟨((List.range D.n).map fun h => lk P 32 h).toArray,
        ((List.range D.n).map fun h => UInt32.ofNat (lk AT 32 h)).toArray,
        ((List.range D.n).map fun h => UInt32.ofNat (lk BT 32 h)).toArray⟩ := by
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, pw2_eq'] at hn
  have hv0 : lk P 32 0 = D.v0 := Nat.eq_of_beq_eq_true hP0
  obtain ⟨hcA, hcB⟩ := colsAB_eq D hA hB hseed
  change vOrbitBFS D.d D.colsA D.colsB D.v0 D.n = _
  rw [← hv0]
  refine vOrbitBFS_sim (sq := seqAt AT BT) (fo := fun h => lk FO 32 h) hn.1 hn.2
    (fun h hh => (orbAt_iff.1 (horb h hh)).1) (fun h hh => (orbAt_iff.1 (horb h hh)).2.1)
    (fun h hh => (orbAt_iff.1 (horb h hh)).2.2.1)
    (fun h hh => by rw [hcA, (orbAt_iff.1 (horb h hh)).2.2.2.1])
    (fun h hh => by rw [hcB, (orbAt_iff.1 (horb h hh)).2.2.2.2])
    (P_inj_of_sort hsort) (seqAt_even AT BT) (seqAt_odd AT BT) (fun y hy1 hyn => ?_)
    (fun y hy1 hyn => ?_) (fun h hh => (bfsAt_iff.1 (hbfs h hh)).2.1)
    (fun h hh => (bfsAt_iff.1 (hbfs h hh)).2.2)
  · rcases (bfsAt_iff.1 (hbfs y hyn)).1 with h0 | h0
    · omega
    · exact ⟨h0.1, h0.2.1⟩
  · rcases (bfsAt_iff.1 (hbfs y (by omega))).1 with h0 | h0
    · omega
    · rcases h0.2.2 with h1 | h1
      · omega
      · exact h1

theorem orbit_ok (D : VecData) {csA csB : List Char} {MA MB NA NB : Nat}
    {P AT BT FO S IP SP : Nat → Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P S IP SP h = true) :
    vOrbitOK D.d D.n D.colsA D.colsB (D.orbit ()) = true := by
  have hO := orbit_eq D hA hB hseed hn hP0 horb hbfs hsort
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, pw2_eq'] at hn
  obtain ⟨hcA, hcB⟩ := colsAB_eq D hA hB hseed
  have hinj := P_inj_of_sort hsort
  have hget : ∀ i < D.n, (D.orbit ()).pts[i]! = lk P 32 i := by
    intro i hi
    rw [hO]
    exact toArray_get hi
  have hap : ∀ (f : Nat → Nat), (∀ i < D.n, f i < D.n) → ∀ i < D.n,
      ap ((List.range D.n).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
    intro f hf i hi
    unfold ap
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by have := hf i hi; omega)
  have hsz : (D.orbit ()).pts.size = D.n := by rw [hO]; simp
  unfold vOrbitOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hsz, by rw [hO]; simp⟩, by rw [hO]; simp⟩, CFSG.KS.TW.allIn_iff.2 fun i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := orbAt_iff.1 (horb i hi)
  have hpos := CFSG.KC.PosTable.posTable_get (d := D.d) (pts := (D.orbit ()).pts)
    (fun j hj => by rw [hget j (by omega)]; exact (orbAt_iff.1 (horb j (by omega))).1)
    (fun j hj k hk e => hinj j (by omega) k (by omega) (by rwa [hget j (by omega), hget k (by omega)] at e))
    (by omega) (i := i) (by omega)
  have ha := hap (fun h => lk AT 32 h) (fun j hj => (orbAt_iff.1 (horb j hj)).2.1) i hi
  have hb := hap (fun h => lk BT 32 h) (fun j hj => (orbAt_iff.1 (horb j hj)).2.2.1) i hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by rw [hget i hi]; exact h1, hpos⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hO]; exact ha ▸ h2
  · rw [hO]
    dsimp only
    rw [ha, toArray_get h2, toArray_get hi, hcA, h4]
  · rw [hO]; exact hb ▸ h3
  · rw [hO]
    dsimp only
    rw [hb, toArray_get h3, toArray_get hi, hcB, h5]

end CFSG.KC.VecK

end
