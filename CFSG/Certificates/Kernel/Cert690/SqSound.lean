module

public import CFSG.GF2Type.Smith1979W3.Cert690.Tab
public import CFSG.Certificates.Kernel.Cert690.CBaseSound
public import Certificates.Data.Kernel.Cert690.Sq

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

@[expose] def dotB (f v : ℕ) : Bool :=
  (f.testBit 0 && v.testBit 0) ^^ (f.testBit 1 && v.testBit 1) ^^ (f.testBit 2 && v.testBit 2) ^^
    (f.testBit 3 && v.testBit 3) ^^ (f.testBit 4 && v.testBit 4) ^^ (f.testBit 5 && v.testBit 5)

@[expose] def cB (g v w : ℕ) : Bool := b0n (Code.act g v) (Code.act g w) ^^ b0n v w

theorem dotB_xor (f v w : ℕ) : dotB f (v ^^^ w) = (dotB f v ^^ dotB f w) := by
  simp only [dotB, Nat.testBit_xor, Bool.and_xor_distrib_left]
  generalize (f.testBit 0 && v.testBit 0) = a0
  generalize (f.testBit 1 && v.testBit 1) = a1
  generalize (f.testBit 2 && v.testBit 2) = a2
  generalize (f.testBit 3 && v.testBit 3) = a3
  generalize (f.testBit 4 && v.testBit 4) = a4
  generalize (f.testBit 5 && v.testBit 5) = a5
  generalize (f.testBit 0 && w.testBit 0) = b0
  generalize (f.testBit 1 && w.testBit 1) = b1
  generalize (f.testBit 2 && w.testBit 2) = b2
  generalize (f.testBit 3 && w.testBit 3) = b3
  generalize (f.testBit 4 && w.testBit 4) = b4
  generalize (f.testBit 5 && w.testBit 5) = b5
  simp only [Bool.xor_left_comm, Bool.xor_comm]

theorem dotB_zero (f : ℕ) : dotB f 0 = false := by simp [dotB]

theorem dotB_two_pow (f : ℕ) {j : ℕ} (hj : j < 6) : dotB f (2 ^ j) = f.testBit j := by
  interval_cases j <;>
  · simp only [dotB]
    generalize f.testBit 0 = a0
    generalize f.testBit 1 = a1
    generalize f.testBit 2 = a2
    generalize f.testBit 3 = a3
    generalize f.testBit 4 = a4
    generalize f.testBit 5 = a5
    revert a0 a1 a2 a3 a4 a5
    decide

theorem sel_xor (v w j c : ℕ) : Code.sel (v ^^^ w) j c = Code.sel v j c ^^^ Code.sel w j c := by
  unfold Code.sel
  rw [Nat.testBit_xor]
  cases v.testBit j <;> cases w.testBit j <;> simp

theorem act_xor (g v w : ℕ) : Code.act g (v ^^^ w) = Code.act g v ^^^ Code.act g w := by
  unfold Code.act
  simp only [sel_xor]
  ac_rfl

theorem b0n_xor_left (u v w : ℕ) : b0n (u ^^^ v) w = (b0n u w ^^ b0n v w) := by
  simp only [b0n, Nat.testBit_xor, Bool.and_xor_distrib_right]
  generalize (u.testBit 1 && w.testBit 0) = a0
  generalize (u.testBit 3 && w.testBit 2) = a1
  generalize (u.testBit 5 && w.testBit 4) = a2
  generalize (v.testBit 1 && w.testBit 0) = b0
  generalize (v.testBit 3 && w.testBit 2) = b1
  generalize (v.testBit 5 && w.testBit 4) = b2
  simp only [Bool.xor_left_comm, Bool.xor_comm]

theorem b0n_xor_right (u v w : ℕ) : b0n u (v ^^^ w) = (b0n u v ^^ b0n u w) := by
  simp only [b0n, Nat.testBit_xor, Bool.and_xor_distrib_left]
  generalize (u.testBit 1 && v.testBit 0) = a0
  generalize (u.testBit 3 && v.testBit 2) = a1
  generalize (u.testBit 5 && v.testBit 4) = a2
  generalize (u.testBit 1 && w.testBit 0) = b0
  generalize (u.testBit 3 && w.testBit 2) = b1
  generalize (u.testBit 5 && w.testBit 4) = b2
  simp only [Bool.xor_left_comm, Bool.xor_comm]

theorem b0n_zero_left (w : ℕ) : b0n 0 w = false := by simp [b0n]

theorem b0n_zero_right (w : ℕ) : b0n w 0 = false := by simp [b0n]

theorem cB_xor_left (g u v w : ℕ) : cB g (u ^^^ v) w = (cB g u w ^^ cB g v w) := by
  simp only [cB, act_xor, b0n_xor_left]
  generalize b0n (Code.act g u) (Code.act g w) = a
  generalize b0n (Code.act g v) (Code.act g w) = b
  generalize b0n u w = c
  generalize b0n v w = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem cB_xor_right (g u v w : ℕ) : cB g u (v ^^^ w) = (cB g u v ^^ cB g u w) := by
  simp only [cB, act_xor, b0n_xor_right]
  generalize b0n (Code.act g u) (Code.act g v) = a
  generalize b0n (Code.act g u) (Code.act g w) = b
  generalize b0n u v = c
  generalize b0n u w = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem cB_zero_left (g w : ℕ) : cB g 0 w = false := by
  simp [cB, act_zero, b0n_zero_left]

theorem cB_zero_right (g w : ℕ) : cB g w 0 = false := by
  simp [cB, act_zero, b0n_zero_right]

theorem qB_false_eq (n : ℕ) : qB false n = b0n n n := by
  simp only [qB, b0n, Bool.false_and, Bool.xor_false, Bool.and_comm]

theorem isoQ_spec {g : ℕ} (hq : isoQ false g = true) {v : ℕ} (hv : v < 64) :
    b0n (Code.act g v) (Code.act g v) = b0n v v := by
  unfold isoQ at hq
  rw [List.all_eq_true] at hq
  have h := hq v (List.mem_range.2 hv)
  rw [beq_iff_eq, qB_false_eq, qB_false_eq] at h
  exact h

theorem cB_self {g : ℕ} (hq : isoQ false g = true) {v : ℕ} (hv : v < 64) : cB g v v = false := by
  rw [cB, isoQ_spec hq hv, Bool.xor_self]

theorem xor_lt64 {v w : ℕ} (hv : v < 64) (hw : w < 64) : v ^^^ w < 64 :=
  Nat.xor_lt_two_pow (n := 6) hv hw

theorem cB_symm {g : ℕ} (hq : isoQ false g = true) {v w : ℕ} (hv : v < 64) (hw : w < 64) :
    cB g v w = cB g w v := by
  have h := cB_self hq (xor_lt64 hv hw)
  rw [cB_xor_left, cB_xor_right, cB_xor_right, cB_self hq hv, cB_self hq hw] at h
  revert h
  cases cB g v w <;> cases cB g w v <;> simp

theorem two_pow_lowIdx_lt (v : ℕ) : 2 ^ lowIdx v < 64 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (lowIdx_lt_six v)) (by norm_num)

theorem fTable_rec (g f : ℕ) {v : ℕ} (hv : v < 64) (hv0 : v ≠ 0) :
    (fTable g f)[v]! = ((fTable g f)[v ^^^ 2 ^ lowIdx v]! ^^ f.testBit (lowIdx v) ^^
      cB g (v ^^^ 2 ^ lowIdx v) (2 ^ lowIdx v)) := by
  rw [fTable_getElem!_succ hv hv0, Nat.one_shiftLeft, cB, Bool.xor_assoc, Bool.xor_assoc]

theorem lowIdx_xor_lt' {v : ℕ} (hv : v ≠ 0) (hv64 : v < 64) : v ^^^ 2 ^ lowIdx v < v := by
  have := lowIdx_xor_lt hv hv64
  rwa [Nat.one_shiftLeft] at this

theorem fTable_twist (g f : ℕ) : ∀ v < 64, (fTable g f)[v]! = ((fTable g 0)[v]! ^^ dotB f v) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [fTable_getElem!_zero, fTable_getElem!_zero, dotB_zero]
      rfl
    · have hw := lowIdx_xor_lt' hv0 hv
      have hve : v = (v ^^^ 2 ^ lowIdx v) ^^^ 2 ^ lowIdx v := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hd : dotB f v = (dotB f (v ^^^ 2 ^ lowIdx v) ^^ f.testBit (lowIdx v)) := by
        conv_lhs => rw [hve]
        rw [dotB_xor, dotB_two_pow f (lowIdx_lt_six v)]
      rw [fTable_rec g f hv hv0, fTable_rec g 0 hv hv0, ih _ hw (by omega), Nat.zero_testBit, hd]
      generalize (fTable g 0)[v ^^^ 2 ^ lowIdx v]! = a
      generalize dotB f (v ^^^ 2 ^ lowIdx v) = b
      generalize f.testBit (lowIdx v) = c
      generalize cB g (v ^^^ 2 ^ lowIdx v) (2 ^ lowIdx v) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl

set_option maxRecDepth 100000 in
theorem lowIdx_xor_of_lt : ∀ x < 64, ∀ j < 6, x ≠ 0 → j < lowIdx x →
    lowIdx (x ^^^ 2 ^ j) = j ∧ x ^^^ 2 ^ j ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem lowIdx_xor_of_gt : ∀ x < 64, ∀ j < 6, x ≠ 0 → lowIdx x < j →
    lowIdx (x ^^^ 2 ^ j) = lowIdx x ∧ x ^^^ 2 ^ j ≠ 0 := by decide +kernel

theorem two_pow_lt64 {j : ℕ} (hj : j < 6) : 2 ^ j < 64 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)

theorem xor_xor_cancel (x y : ℕ) : x ^^^ y ^^^ y = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem fTable_xor_two_pow {g : ℕ} (hq : isoQ false g = true) (f : ℕ) :
    ∀ x < 64, ∀ j < 6, (fTable g f)[x ^^^ 2 ^ j]! =
      ((fTable g f)[x]! ^^ f.testBit j ^^ cB g x (2 ^ j)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx j hj
    by_cases hx0 : x = 0
    · subst hx0
      rw [Nat.zero_xor, fTable_two_pow hj, fTable_getElem!_zero, cB_zero_left]
      cases f.testBit j <;> rfl
    · have hx'lt := lowIdx_xor_lt' hx0 hx
      have hrec := fTable_rec g f hx hx0
      have hk6 := lowIdx_lt_six x
      rcases lt_trichotomy j (lowIdx x) with hjk | hjk | hjk
      · obtain ⟨hl, hne⟩ := lowIdx_xor_of_lt x hx j hj hx0 hjk
        have h := fTable_rec g f (xor_lt64 hx (two_pow_lt64 hj)) hne
        rw [hl, xor_xor_cancel] at h
        exact h
      · subst hjk
        generalize hk : lowIdx x = k at hrec hx'lt hk6 ⊢
        generalize hx' : x ^^^ 2 ^ k = x' at hrec hx'lt ⊢
        have hxx : x = x' ^^^ 2 ^ k := by rw [← hx', xor_xor_cancel]
        have h2 : cB g x (2 ^ k) = cB g x' (2 ^ k) := by
          rw [hxx, cB_xor_left, cB_self hq (two_pow_lt64 hk6), Bool.xor_false]
        rw [hrec, h2]
        generalize (fTable g f)[x']! = a
        generalize f.testBit k = b
        generalize cB g x' (2 ^ k) = c
        cases a <;> cases b <;> cases c <;> rfl
      · obtain ⟨hl, hne⟩ := lowIdx_xor_of_gt x hx j hj hx0 hjk
        have h := fTable_rec g f (xor_lt64 hx (two_pow_lt64 hj)) hne
        rw [hl] at h
        generalize hk : lowIdx x = k at h hrec hx'lt hk6 hjk
        have e1 : x ^^^ 2 ^ j ^^^ 2 ^ k = (x ^^^ 2 ^ k) ^^^ 2 ^ j := by
          rw [Nat.xor_assoc, Nat.xor_comm (2 ^ j), ← Nat.xor_assoc]
        rw [e1] at h
        generalize hx' : x ^^^ 2 ^ k = x' at h hrec hx'lt
        have hxx : x = x' ^^^ 2 ^ k := by rw [← hx', xor_xor_cancel]
        have hx'64 : x' < 64 := by omega
        have c2 : cB g x (2 ^ j) = (cB g x' (2 ^ j) ^^ cB g (2 ^ k) (2 ^ j)) := by
          rw [hxx, cB_xor_left]
        rw [h, ih x' hx'lt hx'64 j hj, hrec, cB_xor_left, c2,
          cB_symm hq (two_pow_lt64 hj) (two_pow_lt64 hk6)]
        generalize (fTable g f)[x']! = a
        generalize f.testBit j = b
        generalize f.testBit k = b'
        generalize cB g x' (2 ^ j) = c
        generalize cB g x' (2 ^ k) = c'
        generalize cB g (2 ^ k) (2 ^ j) = d
        cases a <;> cases b <;> cases b' <;> cases c <;> cases c' <;> cases d <;> rfl

theorem fTable_xor {g : ℕ} (hq : isoQ false g = true) (f : ℕ) :
    ∀ w < 64, ∀ v < 64, (fTable g f)[v ^^^ w]! =
      ((fTable g f)[v]! ^^ (fTable g f)[w]! ^^ cB g v w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw v hv
    by_cases hw0 : w = 0
    · subst hw0
      rw [Nat.xor_zero, fTable_getElem!_zero, cB_zero_right]
      cases (fTable g f)[v]! <;> rfl
    · have hw'lt := lowIdx_xor_lt' hw0 hw
      have hk6 := lowIdx_lt_six w
      generalize lowIdx w = k at hw'lt hk6
      generalize hw' : w ^^^ 2 ^ k = w' at hw'lt
      have hww : w = w' ^^^ 2 ^ k := by rw [← hw', xor_xor_cancel]
      have hw'64 : w' < 64 := by omega
      have e1 : v ^^^ w = (v ^^^ w') ^^^ 2 ^ k := by rw [hww, Nat.xor_assoc]
      have hFw : (fTable g f)[w]! = ((fTable g f)[w']! ^^ f.testBit k ^^ cB g w' (2 ^ k)) := by
        rw [hww]
        exact fTable_xor_two_pow hq f w' hw'64 k hk6
      have hcw : cB g v w = (cB g v w' ^^ cB g v (2 ^ k)) := by rw [hww, cB_xor_right]
      rw [e1, fTable_xor_two_pow hq f _ (xor_lt64 hv hw'64) k hk6, ih w' hw'lt hw'64 v hv,
        cB_xor_left, hFw, hcw]
      generalize (fTable g f)[v]! = a
      generalize (fTable g f)[w']! = b
      generalize f.testBit k = c
      generalize cB g v w' = d
      generalize cB g w' (2 ^ k) = d'
      generalize cB g v (2 ^ k) = d''
      cases a <;> cases b <;> cases c <;> cases d <;> cases d' <;> cases d'' <;> rfl

theorem nondeg_b0n : ∀ z < 64, z ≠ 0 → ∃ u < 64, (b0n z u ^^ b0n u z) = true := by
  decide +kernel

theorem act_injective {g : ℕ} (hq : isoQ false g = true) {v w : ℕ} (hv : v < 64) (hw : w < 64)
    (h : Code.act g v = Code.act g w) : v = w := by
  have hz : Code.act g (v ^^^ w) = 0 := by rw [act_xor, h, Nat.xor_self]
  by_contra hne
  have hz0 : v ^^^ w ≠ 0 := fun e => hne (by
    calc v = v ^^^ w ^^^ w := (xor_xor_cancel v w).symm
      _ = w := by rw [e, Nat.zero_xor])
  obtain ⟨u, hu, hb⟩ := nondeg_b0n _ (xor_lt64 hv hw) hz0
  have hs := cB_symm hq (xor_lt64 hv hw) hu
  rw [cB, cB, hz, b0n_zero_left, b0n_zero_right] at hs
  revert hb hs
  cases b0n (v ^^^ w) u <;> cases b0n u (v ^^^ w) <;> simp

@[expose] def bN (b : Bool) : ℕ := if b then 1 else 0

theorem bN_lt (b : Bool) : bN b < 2 := by cases b <;> decide

theorem xor_lt2 {a b : ℕ} (ha : a < 2) (hb : b < 2) : a ^^^ b < 2 :=
  Nat.xor_lt_two_pow (n := 1) ha hb

theorem liftTab_entry {g f x : ℕ} (hx : x < 128) :
    (liftTab g f)[x]! = (x % 2 ^^^ bN ((fTable g f)[x / 2]!)) + 2 * Code.act g (x / 2) :=
  liftTab_getElem! hx

theorem mk_mod {c u : ℕ} (hc : c < 2) : (c + 2 * u) % 2 = c := by omega

theorem mk_div {c u : ℕ} (hc : c < 2) : (c + 2 * u) / 2 = u := by omega

theorem liftTab_lt {g f x : ℕ} (hx : x < 128) : (liftTab g f)[x]! < 128 := by
  rw [liftTab_entry hx]
  have h1 := xor_lt2 (Nat.mod_lt x (by norm_num : 0 < 2)) (bN_lt ((fTable g f)[x / 2]!))
  have h2 := Code.act_lt g (x / 2)
  omega

theorem qmulN_mk {a v b w : ℕ} (ha : a < 2) (hb : b < 2) :
    qmulN (a + 2 * v) (b + 2 * w) = (a ^^^ b ^^^ bN (b0n v w)) + 2 * (v ^^^ w) := by
  simp only [qmulN, mk_mod ha, mk_div ha, mk_mod hb, mk_div hb]
  rfl

theorem bN_xor (p q : Bool) : bN (p ^^ q) = bN p ^^^ bN q := by
  cases p <;> cases q <;> rfl

theorem liftTab_mul {g : ℕ} (hq : isoQ false g = true) (f : ℕ) {x y : ℕ} (hx : x < 128)
    (hy : y < 128) :
    (liftTab g f)[qmulN x y]! = qmulN ((liftTab g f)[x]!) ((liftTab g f)[y]!) := by
  have hxa : x = x % 2 + 2 * (x / 2) := (Nat.mod_add_div x 2).symm
  have hya : y = y % 2 + 2 * (y / 2) := (Nat.mod_add_div y 2).symm
  have ha := Nat.mod_lt x (by norm_num : 0 < 2)
  have hb := Nat.mod_lt y (by norm_num : 0 < 2)
  have hv : x / 2 < 64 := by omega
  have hw : y / 2 < 64 := by omega
  generalize x % 2 = a at hxa ha
  generalize x / 2 = v at hxa hv
  generalize y % 2 = b at hya hb
  generalize y / 2 = w at hya hw
  subst hxa hya
  have hm : qmulN (a + 2 * v) (b + 2 * w) < 128 := by
    rw [qmulN_mk ha hb]
    have := xor_lt2 (xor_lt2 ha hb) (bN_lt (b0n v w))
    have := xor_lt64 hv hw
    omega
  rw [liftTab_entry hm, liftTab_entry (by omega : a + 2 * v < 128),
    liftTab_entry (by omega : b + 2 * w < 128), qmulN_mk ha hb, mk_mod ha, mk_div ha, mk_mod hb,
    mk_div hb]
  have hab := xor_lt2 (xor_lt2 ha hb) (bN_lt (b0n v w))
  rw [mk_mod hab, mk_div hab, qmulN_mk (xor_lt2 ha (bN_lt _)) (xor_lt2 hb (bN_lt _)), act_xor,
    fTable_xor hq f w hw v hv]
  have key : ∀ p1 p2 p3 p4 : Bool, a ^^^ b ^^^ bN p4 ^^^ bN (p1 ^^ p2 ^^ (p3 ^^ p4)) =
      a ^^^ bN p1 ^^^ (b ^^^ bN p2) ^^^ bN p3 := by
    interval_cases a <;> interval_cases b <;> decide
  rw [cB, key]

theorem liftTab_inj {g : ℕ} (hq : isoQ false g = true) (f : ℕ) {x y : ℕ} (hx : x < 128)
    (hy : y < 128) (h : (liftTab g f)[x]! = (liftTab g f)[y]!) : x = y := by
  rw [liftTab_entry hx, liftTab_entry hy] at h
  have ha := xor_lt2 (Nat.mod_lt x (by norm_num : 0 < 2)) (bN_lt ((fTable g f)[x / 2]!))
  have hb := xor_lt2 (Nat.mod_lt y (by norm_num : 0 < 2)) (bN_lt ((fTable g f)[y / 2]!))
  have h1 := congrArg (· / 2) h
  have h2 := congrArg (· % 2) h
  simp only [mk_div ha, mk_div hb] at h1
  simp only [mk_mod ha, mk_mod hb] at h2
  have hvw : x / 2 = y / 2 := act_injective hq (by omega) (by omega) h1
  rw [hvw] at h2
  have hab : x % 2 = y % 2 := by
    calc x % 2 = x % 2 ^^^ bN ((fTable g f)[y / 2]!) ^^^ bN ((fTable g f)[y / 2]!) :=
          (xor_xor_cancel _ _).symm
      _ = y % 2 := by rw [h2, xor_xor_cancel]
  omega

theorem isHomTab_liftTab {g : ℕ} (hq : isoQ false g = true) (f : ℕ) :
    isHomTabWith (qmulFlat ()) (liftTab g f) = true := by
  unfold isHomTabWith
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨liftTab_size g f, ?_⟩, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    rw [liftTab_size] at hi
    have := liftTab_lt (g := g) (f := f) hi
    rw [getElem!_pos (liftTab g f) i (by rw [liftTab_size]; exact hi)] at this
    simpa using this
  · rw [Array.all_eq_true']
    intro x hx
    rw [Array.all_eq_true']
    intro y hy
    rw [Array.mem_range] at hx hy
    rw [beq_iff_eq, qmulFlat_getElem! hx hy, qmulFlat_getElem! (liftTab_lt hx) (liftTab_lt hy)]
    exact liftTab_mul hq f hx hy
  · rw [card_hashSet]
    have hnd : (liftTab g f).toList.Nodup := by
      rw [List.nodup_iff_injective_get]
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hs : (liftTab g f).toList.length = 128 := by rw [Array.length_toList, liftTab_size]
      have hi' : i < 128 := by omega
      have hj' : j < 128 := by omega
      simp only [List.get_eq_getElem, Array.getElem_toList] at hij
      have e : (liftTab g f)[i]! = (liftTab g f)[j]! := by
        rw [getElem!_pos (liftTab g f) i (by rw [liftTab_size]; exact hi'),
          getElem!_pos (liftTab g f) j (by rw [liftTab_size]; exact hj')]
        exact hij
      exact Fin.ext (liftTab_inj hq f hi' hj' e)
    rw [hnd.dedup, Array.length_toList, liftTab_size]

theorem innW_aux : ∀ e < 128,
    2 * (qmulN (qmulN (qinvN e) 2) e % 2) + qmulN (qmulN (qinvN e) 4) e % 2 +
      8 * (qmulN (qmulN (qinvN e) 8) e % 2) + 4 * (qmulN (qmulN (qinvN e) 16) e % 2) +
      32 * (qmulN (qmulN (qinvN e) 32) e % 2) + 16 * (qmulN (qmulN (qinvN e) 64) e % 2) =
      e / 2 := by
  decide +kernel

theorem innW_innTab {e : ℕ} (he : e < 128) : innW (innTab e) = e / 2 := by
  rw [innW, innTab_getElem! e (by norm_num), innTab_getElem! e (by norm_num),
    innTab_getElem! e (by norm_num), innTab_getElem! e (by norm_num),
    innTab_getElem! e (by norm_num), innTab_getElem! e (by norm_num)]
  exact innW_aux e he

set_option maxRecDepth 100000 in
theorem innTab_even_aux : ∀ e < 128, ∀ i < 128,
    qmulN (qmulN (qinvN (2 * (e / 2))) i) (2 * (e / 2)) = qmulN (qmulN (qinvN e) i) e := by
  decide +kernel

theorem innTab_size (e : ℕ) : (innTab e).size = 128 := by simp [innTab]

theorem innTab_even {e : ℕ} (he : e < 128) : innTab (2 * (e / 2)) = innTab e := by
  apply array_eq_of_getElem!_eq (innTab_size _) (innTab_size _)
  intro i hi
  rw [innTab_getElem! _ hi, innTab_getElem! _ hi]
  exact innTab_even_aux e he i hi

theorem innW_lt (t : Array ℕ) : innW t < 64 := by
  unfold innW
  have := Nat.mod_lt (t[2]!) (by norm_num : 0 < 2)
  have := Nat.mod_lt (t[4]!) (by norm_num : 0 < 2)
  have := Nat.mod_lt (t[8]!) (by norm_num : 0 < 2)
  have := Nat.mod_lt (t[16]!) (by norm_num : 0 < 2)
  have := Nat.mod_lt (t[32]!) (by norm_num : 0 < 2)
  have := Nat.mod_lt (t[64]!) (by norm_num : 0 < 2)
  omega

theorem innTabs_size : (innTabs ()).size = 128 := by simp [innTabs]

theorem findInn_eq_innGuess (t : Array ℕ) : findInn (innTabs ()) t = innGuess t := by
  have hg : 2 * innW t < 128 := by have := innW_lt t; omega
  unfold findInn innGuess
  rw [innTabs_size]
  cases h : (List.range 128).find? (fun e => (innTabs ())[e]! == t) with
  | none =>
    rw [List.find?_eq_none] at h
    have h1 := h (2 * innW t) (List.mem_range.2 hg)
    rw [innTabs_getElem! hg] at h1
    rw [if_neg h1]
  | some e =>
    obtain ⟨hp, i, hi, hie, hmin⟩ := List.find?_eq_some_iff_getElem.1 h
    simp only [List.length_range] at hi
    simp only [List.getElem_range] at hie hmin
    subst hie
    rw [innTabs_getElem! hi, beq_iff_eq] at hp
    have hw : innW t = i / 2 := by rw [← hp, innW_innTab hi]
    have h2 : 2 * (i / 2) = i := by
      by_contra hne
      have hlt : 2 * (i / 2) < i := by omega
      have := hmin _ hlt
      rw [innTabs_getElem! (by omega), innTab_even hi, hp] at this
      simp at this
    rw [hw, h2, if_pos (by rw [hp]; exact beq_self_eq_true t)]

theorem firstMapV_get? {β : Type} (key : ℕ → ℕ) (val : ℕ → β) : ∀ (l : List ℕ)
    (m : Std.HashMap ℕ β) (y : ℕ),
    (l.foldl (fun m j => if m.contains (key j) then m else m.insert (key j) (val j)) m).get? y =
      (m.get? y).or ((l.find? fun j => key j == y).map val)
  | [], m, y => by simp
  | j :: l, m, y => by
    rw [List.foldl_cons, firstMapV_get? key val l, List.find?_cons]
    by_cases hc : m.contains (key j) = true
    · rw [if_pos hc]
      by_cases hk : key j = y
      · subst hk
        have hs : (m.get? (key j)).isSome := by
          rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.isSome_getElem?_eq_contains]
          exact hc
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
        rw [hv]
        rfl
      · have hb : (key j == y) = false := by simpa using hk
        simp only [hb]
    · rw [if_neg hc, Std.HashMap.get?_insert]
      by_cases hk : key j = y
      · subst hk
        have hn : m.get? (key j) = none := by
          rw [Std.HashMap.get?_eq_getElem?, Option.eq_none_iff_forall_ne_some]
          intro v hv
          apply hc
          rw [Std.HashMap.contains_eq_isSome_getElem?, hv]
          rfl
        simp only [beq_self_eq_true, if_true, hn]
        rfl
      · have hb : (key j == y) = false := by simpa using hk
        simp only [hb, Bool.false_eq_true, if_false]

theorem firstMapV_contains {β : Type} (key : ℕ → ℕ) (val : ℕ → β) (l : List ℕ)
    (m : Std.HashMap ℕ β) (y : ℕ) :
    (l.foldl (fun m j => if m.contains (key j) then m else m.insert (key j) (val j)) m).contains y
      = (m.contains y || l.any fun j => key j == y) := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
    firstMapV_get?, Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]
  cases m.get? y with
  | some v => rfl
  | none =>
    simp only [Option.none_or, Option.isSome_map, Option.isSome_none, Bool.false_or]
    cases hf : l.find? (fun j => key j == y) with
    | none =>
      rw [List.find?_eq_none] at hf
      rw [Option.isSome_none, eq_comm, List.any_eq_false]
      intro j hj
      simpa using hf j hj
    | some j =>
      rw [Option.isSome_some, eq_comm, List.any_eq_true]
      exact ⟨j, List.mem_of_find?_eq_some hf, List.find?_some (p := fun j => key j == y) hf⟩

@[expose] def firstConj (E invE : Array ℕ) (i r y : ℕ) : Option (ℕ × ℕ) :=
  ((List.range E.size).find? fun j => Code.mul (Code.mul (E[j]!) r) (invE[j]!) == y).map
    fun j => (i, E[j]!)

theorem classMapOfReps_two_get? (E invE : Array ℕ) (r₁ r₂ y : ℕ) :
    (classMapOfReps E invE #[r₁, r₂]).get? y =
      (firstConj E invE 0 r₁ y).or (firstConj E invE 1 r₂ y) := by
  unfold classMapOfReps firstConj
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [show List.range 2 = [0, 1] from rfl, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  rw [firstMapV_get? (fun j => Code.mul (Code.mul (E[j]!) (#[r₁, r₂][1]!)) (invE[j]!))
    (fun j => (1, E[j]!)), firstMapV_get? (fun j => Code.mul (Code.mul (E[j]!) (#[r₁, r₂][0]!))
    (invE[j]!)) (fun j => (0, E[j]!))]
  simp

theorem classMapOfReps_one_get? (E invE : Array ℕ) (r y : ℕ) :
    (classMapOfReps E invE #[r]).get? y = firstConj E invE 0 r y := by
  unfold classMapOfReps firstConj
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [show List.range 1 = [0] from rfl, List.foldl_cons, List.foldl_nil]
  rw [firstMapV_get? (fun j => Code.mul (Code.mul (E[j]!) (#[r][0]!)) (invE[j]!))
    (fun j => (0, E[j]!))]
  simp

end CFSG.KC.C690

end
