module

public import Certificates.Data.Kernel.SporSch.Co1RankBnd
public import CFSG.Certificates.Kernel.SporSch.Co1RankElSound
public import CFSG.Certificates.Kernel.SporSch.Co1RankRCSound

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC CFSG.KC.Loop CFSG.KC.Co1RankCoord CFSG.KC.Co1RankCand CFSG.KC.Co1RankBnd

@[expose] def bvec (n x : ℕ) : Fin n → ZMod 2 := fun k => if x.testBit k then 1 else 0

theorem bvec_xor (n x y : ℕ) : bvec n (Nat.xor x y) = bvec n x + bvec n y := by
  funext k
  simp only [bvec, Pi.add_apply]
  have e : (Nat.xor x y).testBit k = (x.testBit k ^^ y.testBit k) := Nat.testBit_xor x y k
  rw [e]
  cases x.testBit k <;> cases y.testBit k <;> decide

theorem bvec_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : bvec n x = bvec n y) : x = y := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < n
  · have := congrFun h ⟨k, hk⟩
    simp only [bvec] at this
    cases hx' : x.testBit k <;> cases hy' : y.testBit k <;> rw [hx', hy'] at this <;>
      first | rfl | exact absurd this (by decide)
  · have hd : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hd), Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hd)]

theorem z2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem lor_shift {d p q : ℕ} (hp : p < 2 ^ d) : Nat.lor p (Nat.shiftLeft q d) = 2 ^ d * q + p := by
  change p ||| q <<< d = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hp, Nat.shiftLeft_eq, mul_comm]

theorem lor_shift_lt {d m p q : ℕ} (hp : p < 2 ^ d) (hq : q < 2 ^ m) :
    Nat.lor p (Nat.shiftLeft q d) < 2 ^ (d + m) := by
  rw [lor_shift hp, pow_add]
  have h1 : 2 ^ d * (q + 1) ≤ 2 ^ d * 2 ^ m := Nat.mul_le_mul_left _ hq
  rw [Nat.mul_succ] at h1
  linarith

theorem lor_eq_xor {d p q : ℕ} (hp : p < 2 ^ d) :
    Nat.lor p (Nat.shiftLeft q d) = Nat.xor p (Nat.shiftLeft q d) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  change (p ||| q <<< d).testBit j = (p ^^^ q <<< d).testBit j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hj : j < d
  · simp [show ¬ j ≥ d by omega]
  · have : p.testBit j = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem shl_xor (a b d : ℕ) :
    Nat.shiftLeft (Nat.xor a b) d = Nat.xor (Nat.shiftLeft a d) (Nat.shiftLeft b d) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  change ((a ^^^ b) <<< d).testBit j = (a <<< d ^^^ b <<< d).testBit j
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_xor]
  cases decide (j ≥ d) <;> simp

theorem xor_lt {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : Nat.xor a b < 2 ^ n :=
  Nat.xor_lt_two_pow ha hb

theorem xor4 (a b c e : ℕ) :
    Nat.xor (Nat.xor a b) (Nat.xor c e) = Nat.xor (Nat.xor a c) (Nat.xor b e) := by
  change (a ^^^ b) ^^^ (c ^^^ e) = (a ^^^ c) ^^^ (b ^^^ e)
  rw [Nat.xor_assoc, Nat.xor_assoc, ← Nat.xor_assoc b, ← Nat.xor_assoc c, Nat.xor_comm b c]

theorem phiR_xor (row : ℕ → ℕ) (a b : ℕ) :
    ∀ n, phiR row n (Nat.xor a b) = Nat.xor (phiR row n a) (phiR row n b)
  | 0 => (Nat.xor_zero 0).symm
  | n + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (phiR row n (Nat.xor a b))
        (Nat.xor (phiR row n (Nat.xor a b)) (row n)) (bitB (Nat.xor a b) n) =
      Nat.xor (Bool.rec (motive := fun _ => ℕ) (phiR row n a) (Nat.xor (phiR row n a) (row n))
          (bitB a n))
        (Bool.rec (motive := fun _ => ℕ) (phiR row n b) (Nat.xor (phiR row n b) (row n))
          (bitB b n))
    have e : (Nat.xor a b).testBit n = (a.testBit n ^^ b.testBit n) := Nat.testBit_xor a b n
    rw [bitB_eq, bitB_eq, bitB_eq, e, phiR_xor row a b n]
    have z : Nat.xor (row n) (row n) = 0 := Nat.xor_self _
    cases a.testBit n <;> cases b.testBit n <;> dsimp only [Bool.xor]
    · rfl
    · change _ = (phiR row n a) ^^^ ((phiR row n b) ^^^ row n)
      rw [← Nat.xor_assoc]
      rfl
    · change _ = ((phiR row n a) ^^^ row n) ^^^ (phiR row n b)
      rw [Nat.xor_assoc, Nat.xor_comm (row n), ← Nat.xor_assoc]
      rfl
    · rw [xor4, z]
      exact (Nat.xor_zero _).symm

theorem phi_xor (d PH i a b : ℕ) :
    phi d PH i (Nat.xor a b) = Nat.xor (phi d PH i a) (phi d PH i b) := by
  rw [phi_eq, phi_eq, phi_eq, phiR_xor]

@[expose] noncomputable def blk (C : Co1RankCoord.Dat) (i u : ℕ) : ℕ := Nat.xor u (phi C.d C.PHt i u)

@[expose] noncomputable def lhsL (C : Co1RankCoord.Dat) (gs : List ℕ) (u : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih =>
    Nat.lor (blk C (Nat.shiftRight x C.d) u) (Nat.shiftLeft ih C.d)) gs

theorem lhs_eq (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) (u : ℕ) :
    lhs C j gs u = Nat.lor (blk C j u) (Nat.shiftLeft (lhsL C gs u) C.d) := rfl

theorem blk_lt (C : Co1RankCoord.Dat) (i : ℕ) {u : ℕ} (hu : u < 2 ^ C.d) : blk C i u < 2 ^ C.d :=
  Nat.xor_lt_two_pow hu (phi_lt _ _ _ _)

theorem blk_xor (C : Co1RankCoord.Dat) (i a b : ℕ) :
    blk C i (Nat.xor a b) = Nat.xor (blk C i a) (blk C i b) := by
  rw [blk, blk, blk, phi_xor, xor4]

theorem lhsL_xor (C : Co1RankCoord.Dat) {a b : ℕ} (ha : a < 2 ^ C.d) (hb : b < 2 ^ C.d) :
    ∀ gs : List ℕ, lhsL C gs (Nat.xor a b) = Nat.xor (lhsL C gs a) (lhsL C gs b)
  | [] => (Nat.xor_zero 0).symm
  | x :: gs => by
    change Nat.lor (blk C (Nat.shiftRight x C.d) (Nat.xor a b))
        (Nat.shiftLeft (lhsL C gs (Nat.xor a b)) C.d) =
      Nat.xor (Nat.lor (blk C (Nat.shiftRight x C.d) a) (Nat.shiftLeft (lhsL C gs a) C.d))
        (Nat.lor (blk C (Nat.shiftRight x C.d) b) (Nat.shiftLeft (lhsL C gs b) C.d))
    rw [lor_eq_xor (blk_lt C _ (xor_lt ha hb)), lor_eq_xor (blk_lt C _ ha),
      lor_eq_xor (blk_lt C _ hb), lhsL_xor C ha hb gs, blk_xor, shl_xor, xor4]

theorem lhsL_lt (C : Co1RankCoord.Dat) {u : ℕ} (hu : u < 2 ^ C.d) :
    ∀ gs : List ℕ, lhsL C gs u < 2 ^ (C.d * gs.length)
  | [] => Nat.two_pow_pos _
  | x :: gs => by
    change Nat.lor (blk C (Nat.shiftRight x C.d) u) (Nat.shiftLeft (lhsL C gs u) C.d) < _
    rw [List.length_cons, Nat.mul_succ, add_comm]
    exact lor_shift_lt (blk_lt C _ hu) (lhsL_lt C hu gs)

theorem lhs_lt (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) {u : ℕ} (hu : u < 2 ^ C.d) :
    lhs C j gs u < 2 ^ (C.d * (gs.length + 1)) := by
  rw [lhs_eq, Nat.mul_succ, add_comm]
  exact lor_shift_lt (blk_lt C _ hu) (lhsL_lt C hu gs)

theorem lhs_xor (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) {a b : ℕ} (ha : a < 2 ^ C.d) (hb : b < 2 ^ C.d) :
    lhs C j gs (Nat.xor a b) = Nat.xor (lhs C j gs a) (lhs C j gs b) := by
  rw [lhs_eq, lhs_eq, lhs_eq, lor_eq_xor (blk_lt C _ (xor_lt ha hb)),
    lor_eq_xor (blk_lt C _ ha), lor_eq_xor (blk_lt C _ hb), lhsL_xor C ha hb gs, blk_xor, shl_xor,
    xor4]

theorem lhs_zero (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) : lhs C j gs 0 = 0 := by
  have h := lhs_xor C j gs (Nat.two_pow_pos C.d) (Nat.two_pow_pos C.d)
  have z : Nat.xor 0 0 = 0 := Nat.xor_self 0
  rw [z] at h
  have e : Nat.xor (lhs C j gs 0) (lhs C j gs 0) = 0 := Nat.xor_self _
  rw [← h] at e
  exact e

theorem bvec_zero (n : ℕ) : bvec n 0 = 0 := by
  funext j
  simp [bvec]

theorem lhs_expand (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) (W u : ℕ) :
    ∀ n ≤ C.d, bvec W (lhs C j gs (u % 2 ^ n)) =
      ∑ s ∈ Finset.range n, (if u.testBit s then (1 : ZMod 2) else 0) • bvec W (lhs C j gs (2 ^ s))
  | 0, _ => by
    rw [pow_zero, Nat.mod_one, lhs_zero, bvec_zero, Finset.sum_range_zero]
  | n + 1, hn => by
    have hlt : ∀ m ≤ C.d, ∀ v, v % 2 ^ m < 2 ^ C.d := fun m hm v =>
      lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) (Nat.pow_le_pow_right (by norm_num) hm)
    have h2 : 2 ^ n < 2 ^ C.d := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have e : u % 2 ^ (n + 1) = Nat.xor (u % 2 ^ n) (if u.testBit n then 2 ^ n else 0) := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      have ex : (Nat.xor (u % 2 ^ n) (if u.testBit n then 2 ^ n else 0)).testBit i =
          ((u % 2 ^ n).testBit i ^^ (if u.testBit n then 2 ^ n else 0).testBit i) :=
        Nat.testBit_xor _ _ i
      rw [ex, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      rcases lt_trichotomy i n with h | rfl | h
      · cases u.testBit n <;> simp [h, show i < n + 1 by omega, Nat.testBit_two_pow,
          show n ≠ i by omega]
      · cases hb : u.testBit i <;> simp [hb]
      · cases u.testBit n <;> simp [show ¬ i < n by omega, show ¬ i < n + 1 by omega,
          Nat.testBit_two_pow, show n ≠ i by omega]
    have hb : (if u.testBit n then 2 ^ n else 0) < 2 ^ C.d := by
      split_ifs
      · exact h2
      · exact Nat.two_pow_pos _
    rw [e, lhs_xor C j gs (hlt n (by omega) u) hb, bvec_xor, lhs_expand C j gs W u n (by omega),
      Finset.sum_range_succ]
    congr 1
    cases u.testBit n
    · simp [lhs_zero, bvec_zero]
    · simp

theorem packR_bit (W : ℕ) (R : ℕ → ℕ) (t k : ℕ) (hk : k < W) : ∀ n, (∀ s < n, R s < 2 ^ W) →
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun s acc => Nat.lor acc (Nat.shiftLeft (R s) (Nat.mul W s))) n).testBit (W * t + k) =
      (decide (t < n) && (R t).testBit k)
  | 0, _ => by
    change (0 : ℕ).testBit _ = _
    simp
  | m + 1, hR => by
    change ((Nat.rec (motive := fun _ => ℕ) 0
      (fun s acc => Nat.lor acc (Nat.shiftLeft (R s) (Nat.mul W s))) m) |||
        (R m <<< (W * m))).testBit (W * t + k) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, packR_bit W R t k hk m (fun s hs => hR s (by omega))]
    rcases lt_trichotomy t m with h | rfl | h
    · have h1 : W * (t + 1) ≤ W * m := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h1
      simp [h, show t < m + 1 by omega, show ¬ (W * t + k ≥ W * m) by omega]
    · simp
    · have h1 : W * (m + 1) ≤ W * t := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h1
      have hb : (R m).testBit (W * t + k - W * m) = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (hR m (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hb, show ¬ t < m by omega, show ¬ t < m + 1 by omega]

theorem shl1 (s : ℕ) : Nat.shiftLeft 1 s = 2 ^ s := by
  change 1 <<< s = _
  rw [Nat.one_shiftLeft]

theorem rowsF_bit (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) (t k : ℕ)
    (hk : k < C.d * (gs.length + 1)) :
    (rowsF C j gs (C.d * (gs.length + 1))).testBit (C.d * (gs.length + 1) * t + k) =
      (decide (t < C.d) && (lhs C j gs (2 ^ t)).testBit k) := by
  have e := packR_bit (C.d * (gs.length + 1)) (fun s => lhs C j gs (Nat.shiftLeft 1 s)) t k hk C.d
    (fun s hs => by
      change lhs C j gs (Nat.shiftLeft 1 s) < _
      rw [shl1]
      exact lhs_lt C j gs (Nat.pow_lt_pow_right (by norm_num) hs))
  rw [rowsF, e, shl1]

theorem rowsF_row (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) {t : ℕ} (ht : t < C.d) :
    Co1RankRC.rowV (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) t =
      bvec (C.d * (gs.length + 1)) (lhs C j gs (2 ^ t)) := by
  funext k
  simp only [Co1RankRC.rowV, bvec]
  rw [rowsF_bit C j gs t k k.2, decide_eq_true ht, Bool.true_and]

theorem lenL_eq : ∀ L : List ℕ, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem getL_mem : ∀ (L : List ℕ) (c : ℕ), c < L.length → getL L c ∈ L
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, _ => List.mem_cons_self
  | a :: L, c + 1, h => List.mem_cons_of_mem _ (getL_mem L c (by simp at h; omega))

theorem packL_bit {d : ℕ} {k : ℕ} (hk : k < d) : ∀ (K : List ℕ), (∀ q ∈ K, q < 2 ^ d) → ∀ t,
    (packL d K).testBit (d * t + k) = (K.getD t 0).testBit k
  | [], _, t => by
    change (0 : ℕ).testBit _ = _
    simp
  | q :: K, hK, t => by
    change (Nat.lor q (Nat.shiftLeft (packL d K) d)).testBit _ = _
    rw [lor_shift (hK q List.mem_cons_self), Co1RankRC.testBit_split (hK q List.mem_cons_self)]
    rcases t with _ | t
    · simp [hk]
    · rw [if_neg (by nlinarith), show d * (t + 1) + k - d = d * t + k by rw [Nat.mul_succ]; omega,
        packL_bit hk K (fun q hq => hK q (List.mem_cons_of_mem _ hq)) t]
      simp

theorem packL_row {d : ℕ} {K : List ℕ} (hK : ∀ q ∈ K, q < 2 ^ d) (t : ℕ) :
    Co1RankRC.rowV d (packL d K) t = bvec d (K.getD t 0) := by
  funext k
  simp only [Co1RankRC.rowV, bvec]
  rw [packL_bit k.2 K hK t]

@[expose] noncomputable def rblk (C : Co1RankCoord.Dat) (j x : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.land x (mask C.d)) (phi C.d C.PHt j (Nat.land x (mask C.d))))
    (Nat.xor (nc C.d C.NCt j (Nat.shiftRight x C.d)) (nc C.d C.NCt (Nat.shiftRight x C.d) j))

@[expose] noncomputable def rhsL (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih =>
    strictN (Nat.shiftRight x C.d) fun i => strictN (Nat.land x (mask C.d)) fun v =>
    Nat.lor (Nat.xor (Nat.xor v (phi C.d C.PHt j v)) (Nat.xor (nc C.d C.NCt j i) (nc C.d C.NCt i j)))
      (Nat.shiftLeft ih C.d)) gs

theorem rhs_eq (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) :
    rhs C j gs = Nat.lor (nc C.d C.NCt j j) (Nat.shiftLeft (rhsL C j gs) C.d) := rfl

theorem rhsL_cons (C : Co1RankCoord.Dat) (j x : ℕ) (gs : List ℕ) :
    rhsL C j (x :: gs) = Nat.lor (rblk C j x) (Nat.shiftLeft (rhsL C j gs) C.d) := by
  unfold rhsL
  simp only [strictN_eq]
  rfl

theorem lhs_eq_rhs (C : Co1RankCoord.Dat) (j u : ℕ) (gs : List ℕ)
    (h0 : blk C j u = nc C.d C.NCt j j) (hg : ∀ x ∈ gs, blk C (Nat.shiftRight x C.d) u = rblk C j x) :
    lhs C j gs u = rhs C j gs := by
  rw [lhs_eq, rhs_eq, h0]
  congr 2
  induction gs with
  | nil => rfl
  | cons x gs ih =>
    rw [rhsL_cons, ← hg x List.mem_cons_self, ← ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))]
    rfl

theorem split_inj {d a b a' b' : ℕ} (hb : b < 2 ^ d) (hb' : b' < 2 ^ d)
    (h : a * 2 ^ d + b = a' * 2 ^ d + b') : a = a' ∧ b = b' := by
  have hp : 0 < 2 ^ d := Nat.two_pow_pos d
  have e1 : (a * 2 ^ d + b) / 2 ^ d = a := by
    rw [mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt hb, add_zero]
  have e2 : (a' * 2 ^ d + b') / 2 ^ d = a' := by
    rw [mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt hb', add_zero]
  have ha : a = a' := by rw [← e1, ← e2, h]
  subst ha
  exact ⟨rfl, by omega⟩

theorem xor_rearr {u v P Q N1 N2 : ℕ}
    (h : Nat.xor (Nat.xor v P) N1 = Nat.xor (Nat.xor u Q) N2) :
    Nat.xor u P = Nat.xor (Nat.xor v Q) (Nat.xor N2 N1) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  have h' := congrArg (fun z => z.testBit k) h
  change ((v ^^^ P) ^^^ N1).testBit k = ((u ^^^ Q) ^^^ N2).testBit k at h'
  change (u ^^^ P).testBit k = ((v ^^^ Q) ^^^ (N2 ^^^ N1)).testBit k
  simp only [Nat.testBit_xor] at h' ⊢
  revert h'
  cases u.testBit k <;> cases v.testBit k <;> cases P.testBit k <;> cases Q.testBit k <;>
    cases N1.testBit k <;> cases N2.testBit k <;> decide

theorem sq_facts (C : Co1RankCoord.Dat) {x : ℕ} (h : mulC C x x = 0) :
    kt C.Kt (x >>> C.d) (x >>> C.d) = 0 ∧
      blk C (x >>> C.d) (Nat.land x (mask C.d)) = nc C.d C.NCt (x >>> C.d) (x >>> C.d) := by
  rw [mulC_eq] at h
  obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.1 h
  refine ⟨?_, ?_⟩
  · rcases Nat.mul_eq_zero.1 h1 with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.two_pow_pos _).ne'
  · exact Nat.xor_eq_zero_iff.1 h2

theorem comm_facts (C : Co1RankCoord.Dat) {g x : ℕ} (h : mulC C g x = mulC C x g) :
    kt C.Kt (g >>> C.d) (x >>> C.d) = kt C.Kt (x >>> C.d) (g >>> C.d) ∧
      blk C (Nat.shiftRight g C.d) (Nat.land x (mask C.d)) = rblk C (x >>> C.d) g := by
  rw [mulC_eq, mulC_eq] at h
  obtain ⟨h1, h2⟩ := split_inj (lo_lt _ _ _ _ _) (lo_lt _ _ _ _ _) h
  exact ⟨h1, xor_rearr h2⟩

theorem bAnd_ck {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem strictB_ck (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem rec_get {α : Type} (N : ℕ) (P : ℕ → α → Bool) : ∀ (L : List α) (i0 : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun i => Nat.beq i N)
      (fun e _ ih i => bAnd(P i e, strictB (Nat.succ i) ih)) L i0 = true →
    ∀ i, i0 ≤ i → i < N → ∃ e ∈ L, P i e = true
  | [], i0, h, i, h1, h2 => absurd (Nat.eq_of_beq_eq_true h) (by omega)
  | e :: L, i0, h, i, h1, h2 => by
    obtain ⟨ha, hb⟩ := bAnd_ck h
    rw [strictB_ck] at hb
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨e, List.mem_cons_self, ha⟩
    · obtain ⟨e', he', h'⟩ := rec_get N P L _ hb i hlt h2
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem chkC_mem {D : Co1RankCand.Dat} (h : chkC D = true) {gs : List ℕ} {Ts : ℕ}
    {es : List (ℕ × ℕ × List ℕ × List ℕ)} (hp : (gs, Ts, es) ∈ D.reps) :
    entriesOK D gs Ts (spanL (toC D) gs) (lenL (spanL (toC D) gs)) es = true := by
  unfold chkC at h
  generalize D.reps = R at h hp
  induction R with
  | nil => exact absurd hp List.not_mem_nil
  | cons p R ih =>
    obtain ⟨h1, h2⟩ := bAnd_ck h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact ih h2 hp

theorem bndOK_mem {D : Co1RankCand.Dat} (h : bndOK D = true) {gs : List ℕ} {Ts : ℕ}
    {es : List (ℕ × ℕ × List ℕ × List ℕ)} (hp : (gs, Ts, es) ∈ D.reps) :
    entriesLt (Nat.shiftLeft 1 D.d) es = true := by
  unfold bndOK at h
  generalize D.reps = R at h hp
  induction R with
  | nil => exact absurd hp List.not_mem_nil
  | cons p R ih =>
    obtain ⟨-, h⟩ := bAnd_ck h
    obtain ⟨h1, h2⟩ := bAnd_ck h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact ih h2 hp

theorem entriesLt_mem {m : ℕ} : ∀ es : List (ℕ × ℕ × List ℕ × List ℕ), entriesLt m es = true →
    ∀ a K cs, (1, a, K, cs) ∈ es → a < m
  | [], _, _, _, _, h => absurd h List.not_mem_nil
  | (mode, a', K', cs') :: es, h, a, K, cs, hm => by
    obtain ⟨h1, h2⟩ := bAnd_ck h
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · exact Nat.blt_eq.mp h1
    · exact entriesLt_mem es h2 a K cs hm

theorem listAll_lhs {C : Co1RankCoord.Dat} {j : ℕ} {gs : List ℕ} : ∀ K : List ℕ,
    List.rec (motive := fun _ => Bool) true
      (fun k _ ih => bAnd(Nat.beq (lhs C j gs k) 0, ih)) K = true → ∀ k ∈ K, lhs C j gs k = 0
  | [], _, k, hk => absurd hk List.not_mem_nil
  | k :: K, h, k', hk => by
    obtain ⟨h1, h2⟩ := bAnd_ck h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Nat.eq_of_beq_eq_true h1
    · exact listAll_lhs K h2 k' hk

theorem entryOK_cases {D : Co1RankCand.Dat} {gs : List ℕ} {Ts : ℕ} {El : List ℕ} {nE j mode a : ℕ}
    {K cs : List ℕ} (h : Co1RankCand.entryOK D gs Ts El nE j (mode, a, K, cs) = true) :
    kt D.Kt j j ≠ 0 ∨
    (kt D.Kt (Nat.shiftRight (getL gs a) D.d) j ≠ kt D.Kt j (Nat.shiftRight (getL gs a) D.d) ∧
      a < lenL gs) ∨
    rankRC (Nat.succ D.d) (Nat.mul D.d (Nat.succ (lenL gs)))
        (Nat.lor (rowsF (toC D) j gs (Nat.mul D.d (Nat.succ (lenL gs))))
          (Nat.shiftLeft (rhs (toC D) j gs) (Nat.mul (Nat.mul D.d (Nat.succ (lenL gs))) D.d))) =
      Nat.succ (rankRC D.d (Nat.mul D.d (Nat.succ (lenL gs)))
        (rowsF (toC D) j gs (Nat.mul D.d (Nat.succ (lenL gs))))) ∨
    (mode = 1 ∧ lhs (toC D) j gs a = rhs (toC D) j gs ∧ (∀ k ∈ K, lhs (toC D) j gs k = 0) ∧
      rankRC D.d (Nat.mul D.d (Nat.succ (lenL gs)))
        (rowsF (toC D) j gs (Nat.mul D.d (Nat.succ (lenL gs)))) + lenL K = D.d ∧
      rankRC (lenL K) D.d (packL D.d K) = lenL K ∧
      Co1RankCand.codesOK D Ts El nE j K a cs = true) := by
  unfold Co1RankCand.entryOK at h
  dsimp only at h
  cases h3 : Nat.beq mode 3
  · rw [h3] at h
    dsimp only at h
    cases h0 : Nat.beq mode 0
    · rw [h0] at h
      dsimp only at h
      obtain ⟨hk, h⟩ := bAnd_ck h
      simp only [strictB_ck] at h
      cases h2 : Nat.beq mode 2
      · rw [h2] at h
        dsimp only at h
        obtain ⟨hm1, h⟩ := bAnd_ck h
        obtain ⟨hl, h⟩ := bAnd_ck h
        obtain ⟨hK, h⟩ := bAnd_ck h
        obtain ⟨hr, h⟩ := bAnd_ck h
        obtain ⟨hKr, hc⟩ := bAnd_ck h
        exact Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true hm1, Nat.eq_of_beq_eq_true hl,
          listAll_lhs K hK, Nat.eq_of_beq_eq_true hr, Nat.eq_of_beq_eq_true hKr, hc⟩))
      · rw [h2] at h
        dsimp only at h
        exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h)))
    · rw [h0] at h
      dsimp only at h
      simp only [strictB_ck] at h
      cases hb : Nat.beq (kt D.Kt (Nat.shiftRight (getL gs a) D.d) j)
          (kt D.Kt j (Nat.shiftRight (getL gs a) D.d))
      · rw [hb] at h
        dsimp only at h
        refine Or.inr (Or.inl ⟨fun e => ?_, Nat.blt_eq.mp h⟩)
        rw [e, Nat.beq_refl] at hb
        exact absurd hb (by decide)
      · rw [hb] at h
        dsimp only at h
        exact absurd h (by decide)
  · rw [h3] at h
    dsimp only at h
    refine Or.inl fun hk => ?_
    rw [hk] at h
    exact absurd h (by decide)

theorem codeOK_cases {D : Co1RankCand.Dat} {Ts : ℕ} {El : List ℕ} {y c : ℕ}
    (h : Co1RankCand.codeOK D Ts El (lenL El) y c = true) :
    y ∈ El ∨ (∃ e ∈ El, in2A D (mulC (toC D) e y) = true) ∨
      ∃ p, Ts / 2 ^ p % 2 = 1 ∧ D.UC / 2 ^ ((D.d + 7) * (p % D.nU)) % 2 ^ (D.d + 7) = y := by
  unfold Co1RankCand.codeOK at h
  cases h1 : Nat.blt c (lenL El)
  · rw [h1] at h
    dsimp only at h
    have hc1 : ¬ c < El.length := fun hc => by
      rw [Nat.blt_eq.mpr (by rw [lenL_eq]; exact hc)] at h1
      exact absurd h1 (by decide)
    cases h2 : Nat.blt c (Nat.add (lenL El) (lenL El))
    · rw [h2] at h
      dsimp only at h
      simp only [strictB_ck] at h
      obtain ⟨h3, h4⟩ := bAnd_ck h
      refine Or.inr (Or.inr ⟨Nat.sub c (Nat.add (lenL El) (lenL El)), ?_, ?_⟩)
      · have e := Nat.eq_of_beq_eq_true h4
        change (Ts >>> _) &&& 1 = 1 at e
        rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at e
        exact e
      · have e := Nat.eq_of_beq_eq_true h3
        rw [land_mask] at e
        change D.UC >>> _ % _ = y at e
        rw [Nat.shiftRight_eq_div_pow] at e
        exact e
    · rw [h2] at h
      dsimp only at h
      have hc2 : c < lenL El + lenL El := Nat.blt_eq.mp h2
      rw [lenL_eq] at hc2
      refine Or.inr (Or.inl ⟨_, getL_mem El _ ?_, h⟩)
      rw [lenL_eq]
      change c - El.length < El.length
      omega
  · rw [h1] at h
    dsimp only at h
    have e := Nat.eq_of_beq_eq_true h
    have hc : c < El.length := by rw [← lenL_eq]; exact Nat.blt_eq.mp h1
    rw [← e]
    exact Or.inl (getL_mem El c hc)

theorem lor_zero_left {a b : ℕ} (h : Nat.lor a b = 0) : a = 0 :=
  (Nat.or_eq_zero_iff.1 h).1

theorem lhs_zero_lt {C : Co1RankCoord.Dat} {j : ℕ} {gs : List ℕ} {k : ℕ} (h : lhs C j gs k = 0) :
    k < 2 ^ C.d := by
  rw [lhs_eq] at h
  have h2 : k = phi C.d C.PHt j k := Nat.xor_eq_zero_iff.1 (lor_zero_left h)
  rw [h2]
  exact phi_lt _ _ _ _

noncomputable def Lm (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) (W : ℕ) :
    (Fin C.d → ZMod 2) →ₗ[ZMod 2] (Fin W → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (fun s : Fin C.d => bvec W (lhs C j gs (2 ^ (s : ℕ))))

theorem Lm_apply (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) (W : ℕ) {u : ℕ} (hu : u < 2 ^ C.d) :
    Lm C j gs W (bvec C.d u) = bvec W (lhs C j gs u) := by
  rw [Lm, Fintype.linearCombination_apply]
  have e := lhs_expand C j gs W u C.d le_rfl
  rw [Nat.mod_eq_of_lt hu] at e
  rw [e, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem span_rows (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) :
    Submodule.span (ZMod 2) (Set.range fun t : Fin C.d =>
      Co1RankRC.rowV (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) t) =
      LinearMap.range (Lm C j gs (C.d * (gs.length + 1))) := by
  rw [Lm, Fintype.range_linearCombination]
  have e : (fun t : Fin C.d =>
      Co1RankRC.rowV (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) t) =
      fun s : Fin C.d => bvec (C.d * (gs.length + 1)) (lhs C j gs (2 ^ (s : ℕ))) :=
    funext fun t => rowsF_row C j gs t.2
  rw [e]

theorem mode2_false (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) {u : ℕ} (hu : u < 2 ^ C.d)
    (h : rankRC (C.d + 1) (C.d * (gs.length + 1))
        (Nat.lor (rowsF C j gs (C.d * (gs.length + 1)))
          (Nat.shiftLeft (lhs C j gs u) (Nat.mul (C.d * (gs.length + 1)) C.d))) =
      rankRC C.d (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) + 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  generalize hW : C.d * (gs.length + 1) = W at h
  have hb : ∀ t k, k < W → (Nat.lor (rowsF C j gs W)
      (Nat.shiftLeft (lhs C j gs u) (Nat.mul W C.d))).testBit (W * t + k) =
      ((decide (t < C.d) && (lhs C j gs (2 ^ t)).testBit k) ||
        (decide (t = C.d) && (lhs C j gs u).testBit k)) := by
    intro t k hk
    change (rowsF C j gs W ||| lhs C j gs u <<< (W * C.d)).testBit (W * t + k) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    subst hW
    rw [rowsF_bit C j gs t k hk]
    congr 1
    rcases lt_trichotomy t C.d with ht | ht | ht
    · have h1 : C.d * (gs.length + 1) * (t + 1) ≤ C.d * (gs.length + 1) * C.d :=
        Nat.mul_le_mul_left _ ht
      rw [Nat.mul_succ] at h1
      simp [show ¬ (C.d * (gs.length + 1) * t + k ≥ C.d * (gs.length + 1) * C.d) by omega,
        show t ≠ C.d by omega]
    · rw [ht]
      simp
    · have h1 : C.d * (gs.length + 1) * (C.d + 1) ≤ C.d * (gs.length + 1) * t :=
        Nat.mul_le_mul_left _ ht
      rw [Nat.mul_succ] at h1
      have hl : (lhs C j gs u).testBit
          (C.d * (gs.length + 1) * t + k - C.d * (gs.length + 1) * C.d) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (lhs_lt C j gs hu)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hl, show t ≠ C.d by omega]
  generalize hA' : Nat.lor (rowsF C j gs W) (Nat.shiftLeft (lhs C j gs u) (Nat.mul W C.d)) = A'
    at h hb
  have hrow1 : ∀ t < C.d, Co1RankRC.rowV W A' t = Co1RankRC.rowV W (rowsF C j gs W) t := by
    intro t ht
    funext k
    simp only [Co1RankRC.rowV]
    subst hW
    rw [hb t k k.2, rowsF_bit C j gs t k k.2]
    simp [show t ≠ C.d by omega]
  have hrow2 : Co1RankRC.rowV W A' C.d = bvec W (lhs C j gs u) := by
    funext k
    simp only [Co1RankRC.rowV, bvec]
    rw [hb C.d k k.2]
    simp
  have hS : Submodule.span (ZMod 2) (Set.range fun t : Fin (C.d + 1) => Co1RankRC.rowV W A' t) =
      Submodule.span (ZMod 2) (Set.range fun t : Fin C.d =>
        Co1RankRC.rowV W (rowsF C j gs W) t) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      dsimp only
      by_cases ht : (t : ℕ) < C.d
      · rw [hrow1 t ht]
        exact Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
      · have htd : (t : ℕ) = C.d := by
          have := t.2
          omega
        rw [htd, hrow2]
        subst hW
        rw [span_rows C j gs, ← Lm_apply C j gs _ hu]
        exact LinearMap.mem_range_self _ _
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      dsimp only
      rw [← hrow1 t t.2]
      exact Submodule.subset_span ⟨Fin.castSucc t, rfl⟩
  rw [Co1RankRC.rankRC_eq, Co1RankRC.rankRC_eq] at h
  unfold Co1RankRC.rk at h
  rw [hS] at h
  omega

theorem mem_getD : ∀ (K : List ℕ) (t : ℕ), t < K.length → K.getD t 0 ∈ K
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: K, 0, _ => by simp
  | a :: K, t + 1, h => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (mem_getD K t (by simp at h; omega))

theorem exists_getD : ∀ (K : List ℕ) (k : ℕ), k ∈ K → ∃ t < K.length, K.getD t 0 = k
  | [], _, h => absurd h List.not_mem_nil
  | a :: K, k, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨t, ht, e⟩ := exists_getD K k h
      exact ⟨t + 1, by simp [ht], by rw [List.getD_cons_succ, e]⟩

theorem packL_range {d : ℕ} {K : List ℕ} (hK : ∀ q ∈ K, q < 2 ^ d) :
    (Set.range fun t : Fin (lenL K) => Co1RankRC.rowV d (packL d K) t) = bvec d '' {k | k ∈ K} := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    have ht : (t : ℕ) < K.length := by
      rw [← lenL_eq]
      exact t.2
    exact ⟨K.getD t 0, mem_getD K t ht, (packL_row hK t).symm⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨t, ht, rfl⟩ := exists_getD K k hk
    exact ⟨⟨t, by rw [lenL_eq]; exact ht⟩, packL_row hK t⟩

theorem spanK_cons (k : ℕ) (K : List ℕ) (q idx : ℕ) : spanK (k :: K) q idx =
    spanK K (Bool.rec (motive := fun _ => ℕ) q (Nat.xor q k) (Nat.beq (Nat.land idx 1) 1))
      (Nat.shiftRight idx 1) := rfl

theorem spanK_even (k : ℕ) (K : List ℕ) (q i : ℕ) : spanK (k :: K) q (2 * i) = spanK K q i := by
  rw [spanK_cons]
  have h1 : Nat.land (2 * i) 1 = 0 := by
    change (2 * i) &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega
  have h2 : Nat.shiftRight (2 * i) 1 = i := by
    change (2 * i) >>> 1 = i
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    omega
  rw [h1, h2]
  rfl

theorem spanK_odd (k : ℕ) (K : List ℕ) (q i : ℕ) :
    spanK (k :: K) q (2 * i + 1) = spanK K (Nat.xor q k) i := by
  rw [spanK_cons]
  have h1 : Nat.land (2 * i + 1) 1 = 1 := by
    change (2 * i + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]
    omega
  have h2 : Nat.shiftRight (2 * i + 1) 1 = i := by
    change (2 * i + 1) >>> 1 = i
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    omega
  rw [h1, h2]
  rfl

theorem spanK_sol (d : ℕ) : ∀ (K : List ℕ), (∀ k ∈ K, k < 2 ^ d) → ∀ q, q < 2 ^ d →
    ∀ w ∈ Submodule.span (ZMod 2) (bvec d '' {k | k ∈ K}),
      ∃ idx < 2 ^ K.length, spanK K q idx < 2 ^ d ∧ bvec d (spanK K q idx) = bvec d q + w
  | [], _, q, hq, w, hw => by
    have e : bvec d '' {k | k ∈ ([] : List ℕ)} = ∅ := by simp
    rw [e, Submodule.span_empty, Submodule.mem_bot] at hw
    refine ⟨0, by simp, hq, ?_⟩
    rw [hw, add_zero]
    rfl
  | k :: K, hK, q, hq, w, hw => by
    have e : bvec d '' {x | x ∈ k :: K} = insert (bvec d k) (bvec d '' {x | x ∈ K}) := by
      ext v
      simp [or_and_right, exists_or, eq_comm]
    rw [e, Submodule.mem_span_insert] at hw
    obtain ⟨c, z, hz, rfl⟩ := hw
    have hk := hK k List.mem_cons_self
    have hK' : ∀ x ∈ K, x < 2 ^ d := fun x hx => hK x (List.mem_cons_of_mem _ hx)
    rcases z2_cases c with rfl | rfl
    · obtain ⟨i, hi, hlt, hv⟩ := spanK_sol d K hK' q hq z hz
      refine ⟨2 * i, ?_, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        omega
      · rw [spanK_even]
        exact hlt
      · rw [spanK_even, hv, zero_smul, zero_add]
    · obtain ⟨i, hi, hlt, hv⟩ := spanK_sol d K hK' (Nat.xor q k) (xor_lt hq hk) z hz
      refine ⟨2 * i + 1, ?_, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        omega
      · rw [spanK_odd]
        exact hlt
      · rw [spanK_odd, hv, bvec_xor, one_smul, add_assoc]

theorem mode1_sol (C : Co1RankCoord.Dat) (j : ℕ) (gs : List ℕ) {u a : ℕ} {K : List ℕ}
    (hu : u < 2 ^ C.d) (ha : a < 2 ^ C.d) (heq : lhs C j gs u = lhs C j gs a)
    (hK : ∀ k ∈ K, lhs C j gs k = 0)
    (hrk : rankRC C.d (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) + lenL K = C.d)
    (hKr : rankRC (lenL K) C.d (packL C.d K) = lenL K) :
    ∃ idx < 2 ^ K.length, spanK K a idx = u := by
  have hKlt : ∀ k ∈ K, k < 2 ^ C.d := fun k hk => lhs_zero_lt (hK k hk)
  have hrange : Module.finrank (ZMod 2) (LinearMap.range (Lm C j gs (C.d * (gs.length + 1)))) =
      rankRC C.d (C.d * (gs.length + 1)) (rowsF C j gs (C.d * (gs.length + 1))) := by
    rw [Co1RankRC.rankRC_eq, Co1RankRC.rk, span_rows C j gs]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (Lm C j gs (C.d * (gs.length + 1)))) =
      lenL K := by
    have e := LinearMap.finrank_range_add_finrank_ker (Lm C j gs (C.d * (gs.length + 1)))
    rw [Module.finrank_fin_fun (R := ZMod 2), hrange] at e
    omega
  have hSK : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (bvec C.d '' {k | k ∈ K})) =
      lenL K := by
    rw [← packL_range hKlt]
    have e := hKr
    rw [Co1RankRC.rankRC_eq, Co1RankRC.rk] at e
    exact e
  have hle : Submodule.span (ZMod 2) (bvec C.d '' {k | k ∈ K}) ≤
      LinearMap.ker (Lm C j gs (C.d * (gs.length + 1))) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    change Lm C j gs (C.d * (gs.length + 1)) (bvec C.d k) = 0
    rw [Lm_apply C j gs _ (hKlt k hk), hK k hk, bvec_zero]
  have hEq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hSK, hker])
  have hmem : bvec C.d (Nat.xor u a) ∈ Submodule.span (ZMod 2) (bvec C.d '' {k | k ∈ K}) := by
    rw [hEq, LinearMap.mem_ker, Lm_apply C j gs _ (xor_lt hu ha), lhs_xor C j gs hu ha, heq]
    have z : Nat.xor (lhs C j gs a) (lhs C j gs a) = 0 := Nat.xor_self _
    rw [z, bvec_zero]
  obtain ⟨idx, hidx, hlt, hv⟩ := spanK_sol C.d K hKlt a ha _ hmem
  refine ⟨idx, hidx, bvec_inj hlt hu ?_⟩
  rw [hv, bvec_xor]
  funext i
  simp only [Pi.add_apply]
  generalize bvec C.d a i = p
  generalize bvec C.d u i = q
  revert p q
  decide

theorem lor_hi {d j u : ℕ} (hu : u < 2 ^ d) : Nat.lor (Nat.shiftLeft j d) u = j * 2 ^ d + u := by
  change j <<< d ||| u = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt hu, Nat.shiftLeft_eq]

theorem split_eq (d x : ℕ) : x = x >>> d * 2 ^ d + Nat.land x (mask d) := by
  rw [land_mask, Nat.shiftRight_eq_div_pow]
  exact (Nat.div_add_mod' x (2 ^ d)).symm

theorem shr_split {d j u : ℕ} (hu : u < 2 ^ d) : (j * 2 ^ d + u) >>> d = j := by
  rw [Nat.shiftRight_eq_div_pow, mul_comm, Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt hu,
    add_zero]

theorem land_split {d j u : ℕ} (hu : u < 2 ^ d) : Nat.land (j * 2 ^ d + u) (mask d) = u := by
  rw [land_mask, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]

theorem chkC_cand {D : Co1RankCand.Dat} (h : chkC D = true) (hb : bndOK D = true)
    {gs : List Nat} {Ts : Nat} {es : List (Nat × Nat × List Nat × List Nat)}
    (hp : (gs, Ts, es) ∈ D.reps) {x : Nat} (hx : x < 2 ^ (D.d + 7))
    (hsq : mulC (Co1RankCand.toC D) x x = 0)
    (hc : ∀ g ∈ gs, mulC (Co1RankCand.toC D) g x = mulC (Co1RankCand.toC D) x g) :
    x ∈ spanL (Co1RankCand.toC D) gs ∨
      (∃ e ∈ spanL (Co1RankCand.toC D) gs, in2A D (mulC (Co1RankCand.toC D) e x) = true) ∨
      ∃ p, Ts / 2 ^ p % 2 = 1 ∧ D.UC / 2 ^ ((D.d + 7) * (p % D.nU)) % 2 ^ (D.d + 7) = x := by
  have hj : x >>> D.d < 128 := shiftRight_lt hx
  have hu : Nat.land x (mask D.d) < 2 ^ D.d := land_mask_lt _ _
  have hxs := split_eq D.d x
  generalize x >>> D.d = j at hj hxs
  generalize Nat.land x (mask D.d) = u at hu hxs
  subst hxs
  have e1 : (j * 2 ^ D.d + u) >>> (toC D).d = j := shr_split hu
  have e2 : Nat.land (j * 2 ^ D.d + u) (mask (toC D).d) = u := land_split hu
  obtain ⟨hk0, hb0⟩ := sq_facts (toC D) hsq
  rw [e1] at hk0
  rw [e1, e2] at hb0
  have hgen : ∀ g ∈ gs, kt (toC D).Kt (g >>> (toC D).d) j = kt (toC D).Kt j (g >>> (toC D).d) ∧
      blk (toC D) (Nat.shiftRight g (toC D).d) u = rblk (toC D) j g := by
    intro g hg
    have e := comm_facts (toC D) (hc g hg)
    rw [e1, e2] at e
    exact e
  have hLR : lhs (toC D) j gs u = rhs (toC D) j gs :=
    lhs_eq_rhs (toC D) j u gs hb0 fun g hg => (hgen g hg).2
  obtain ⟨⟨mode, a, K, cs⟩, hmem, he⟩ := rec_get 128 (fun j e => Co1RankCand.entryOK D gs Ts
    (spanL (toC D) gs) (lenL (spanL (toC D) gs)) j e) es 0 (chkC_mem h hp) j (Nat.zero_le _) hj
  rcases entryOK_cases he with h3 | ⟨h0, ha⟩ | h2 | ⟨rfl, hla, hK0, hrk, hKr, hcodes⟩
  · exact absurd hk0 h3
  · have hg : getL gs a ∈ gs := getL_mem gs a (by rw [← lenL_eq]; exact ha)
    exact absurd (hgen _ hg).1 h0
  · rw [lenL_eq gs, ← hLR] at h2
    exact (mode2_false (toC D) j gs hu h2).elim
  · have ha : a < 2 ^ (toC D).d := by
      have := entriesLt_mem es (bndOK_mem hb hp) a K cs hmem
      rw [shl1] at this
      exact this
    rw [lenL_eq gs] at hrk
    obtain ⟨idx, hidx, hsp⟩ := mode1_sol (toC D) j gs hu ha (hLR.trans hla.symm) hK0 hrk hKr
    obtain ⟨c, -, hc'⟩ := rec_get (Nat.shiftLeft 1 (lenL K)) (fun idx c => Co1RankCand.codeOK D Ts
      (spanL (toC D) gs) (lenL (spanL (toC D) gs)) (Nat.lor (Nat.shiftLeft j D.d) (spanK K a idx)) c)
      cs 0 hcodes idx (Nat.zero_le _) (by rw [shl1, lenL_eq]; exact hidx)
    rw [hsp, lor_hi hu] at hc'
    exact codeOK_cases hc'

end CFSG.KS.SporSch.Co1Rank

end
