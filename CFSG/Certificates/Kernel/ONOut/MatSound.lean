module

public import Certificates.Data.Kernel.ONOut.Mat
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.ONOut

open CFSG.KC.ONOut CFSG.KC.Ord CFSG.KC.Loop CFSG.KS.Mat3

@[expose] def d27v (c : Nat) : Nat := if c < 58 then c - 48 else c - 55

@[expose] def tri (cs : List Char) (k : Nat) : Nat :=
  d27v (cs.getD (k / 3) ' ').toNat / 3 ^ (k % 3) % 3

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem d27_eq (c : Nat) : d27 c = d27v c := by
  unfold d27 d27v
  by_cases h : c < 58
  · rw [if_pos h, Nat.blt_eq.mpr h]
    rfl
  · have : Nat.blt c 58 = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact h (Nat.blt_eq.mp h')
    rw [if_neg h, this]
    rfl

theorem bitK_eq (M p : Nat) : bitK M p = if M.testBit p then 1 else 0 := by
  unfold bitK
  change (M >>> p) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_lt (M / 2 ^ p) (by norm_num : 0 < 2)
  by_cases h : M / 2 ^ p % 2 = 1
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem beq_bit {M p t : Nat} (h : Nat.beq (bitK M p) t = true) (ht : t < 2) :
    M.testBit p = decide (t = 1) := by
  rw [Nat.beq_eq, bitK_eq] at h
  by_cases hb : M.testBit p
  · rw [if_pos hb] at h
    rw [hb, ← h]
    rfl
  · rw [if_neg hb] at h
    rw [Bool.eq_false_iff.mpr hb, ← h]
    rfl

theorem tritOK_sound {s n N M k t : Nat} (h : tritOK s n N M k t = true) (hk : k < n) (ht : t < 3) :
    M.testBit (s * k) = decide (t = 1) ∧ M.testBit (N + s * k) = decide (t = 2) := by
  unfold tritOK at h
  rw [Nat.blt_eq.mpr hk] at h
  obtain ⟨h1, h2⟩ := andB_true3 h
  have h1' : Nat.beq (bitK M (s * k)) (t % 2) = true := h1
  have h2' : Nat.beq (bitK M (N + s * k)) (t / 2) = true := h2
  refine ⟨?_, ?_⟩
  · rw [beq_bit h1' (Nat.mod_lt _ (by norm_num))]
    interval_cases t <;> rfl
  · rw [beq_bit h2' (by omega)]
    interval_cases t <;> rfl

theorem run27_cons (s n N M : Nat) (ch : Char) (cs : List Char) (q : Nat) :
    run27 s n N M (ch :: cs) q = andB (Nat.blt ch.toNat 128)
      (andB (charOK s n N M q ch.toNat) (strictB (Nat.succ q) (run27 s n N M cs))) := rfl

theorem tri_cons_lt (ch : Char) (cs : List Char) {k : Nat} (hk : k < 3) :
    tri (ch :: cs) k = d27v ch.toNat / 3 ^ k % 3 := by
  unfold tri
  rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
  rfl

theorem tri_cons_ge (ch : Char) (cs : List Char) {k : Nat} (hk : 3 ≤ k) :
    tri (ch :: cs) k = tri cs (k - 3) := by
  unfold tri
  have e1 : k / 3 = (k - 3) / 3 + 1 := by omega
  have e2 : k % 3 = (k - 3) % 3 := by omega
  rw [e1, e2, List.getD_cons_succ]

theorem run27_aux {s n N M : Nat} : ∀ (cs : List Char) (q : Nat), run27 s n N M cs q = true →
    (∀ c ∈ cs, c.toNat < 128) ∧ n ≤ 3 * (q + cs.length) ∧
      ∀ k, 3 * q ≤ k → k < n → M.testBit (s * k) = decide (tri cs (k - 3 * q) = 1) ∧
        M.testBit (N + s * k) = decide (tri cs (k - 3 * q) = 2)
  | [], q, h => by
    have hn : n ≤ 3 * q := Nat.le_of_ble_eq_true h
    exact ⟨fun c hc => absurd hc List.not_mem_nil, by simpa using hn, fun k hk hkn => by omega⟩
  | ch :: cs, q, h => by
    rw [run27_cons] at h
    obtain ⟨hc, h⟩ := andB_true3 h
    obtain ⟨hch, h⟩ := andB_true3 h
    rw [strictB_eq] at h
    obtain ⟨ih1, ih2, ih3⟩ := run27_aux cs (q + 1) h
    have hc' : ch.toNat < 128 := Nat.blt_eq.mp hc
    refine ⟨fun c hc2 => ?_, ?_, fun k hk hkn => ?_⟩
    · rcases List.mem_cons.1 hc2 with rfl | hc2
      · exact hc'
      · exact ih1 c hc2
    · rw [List.length_cons]
      omega
    · unfold charOK at hch
      rw [d27_eq] at hch
      obtain ⟨t0, hch⟩ := andB_true3 hch
      obtain ⟨t1, t2⟩ := andB_true3 hch
      by_cases hk3 : k < 3 * q + 3
      · rw [tri_cons_lt ch cs (by omega)]
        have h3 : (3 : Nat) ^ 2 = 9 := by norm_num
        rcases (by omega : k = 3 * q ∨ k = 3 * q + 1 ∨ k = 3 * q + 2) with e | e | e
        · subst e
          rw [Nat.sub_self, pow_zero, Nat.div_one]
          exact tritOK_sound t0 hkn (Nat.mod_lt _ (by norm_num))
        · subst e
          rw [show 3 * q + 1 - 3 * q = 1 by omega, pow_one]
          exact tritOK_sound t1 hkn (Nat.mod_lt _ (by norm_num))
        · subst e
          rw [show 3 * q + 2 - 3 * q = 2 by omega, h3]
          exact tritOK_sound t2 hkn (Nat.mod_lt _ (by norm_num))
      · rw [tri_cons_ge ch cs (by omega), show k - 3 * q - 3 = k - 3 * (q + 1) by omega]
        exact ih3 k (by omega) hkn

theorem run27_sound {s n N M : Nat} {cs : List Char} (h : run27 s n N M cs 0 = true) :
    (∀ c ∈ cs, c.toNat < 128) ∧ n ≤ 3 * cs.length ∧
      ∀ k < n, M.testBit (s * k) = decide (tri cs k = 1) ∧
        M.testBit (N + s * k) = decide (tri cs k = 2) := by
  obtain ⟨h1, h2, h3⟩ := run27_aux cs 0 h
  refine ⟨h1, by simpa using h2, fun k hk => ?_⟩
  have := h3 k (by omega) hk
  rwa [Nat.mul_zero, Nat.sub_zero] at this

theorem tri_lt (cs : List Char) (k : Nat) : tri cs k < 3 := Nat.mod_lt _ (by norm_num)

theorem bv_tri {t : Nat} (ht : t < 3) : bv (decide (t = 1)) (decide (t = 2)) = (t : ZMod 3) := by
  interval_cases t <;> rfl

theorem mat27_sound {d N M : Nat} {cs : List Char} (hN : N = d * d)
    (h : run27 1 N N M cs 0 = true) :
    (∀ c ∈ cs, c.toNat < 128) ∧ N ≤ 3 * cs.length ∧
      ∀ i j : Fin d, mat3 d N M i j = (tri cs (d * i.val + j.val) : ZMod 3) := by
  obtain ⟨h1, h2, h3⟩ := run27_sound h
  refine ⟨h1, h2, fun i j => ?_⟩
  have hk : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
  obtain ⟨b1, b2⟩ := h3 _ hk
  rw [Nat.one_mul] at b1 b2
  unfold mat3
  rw [b1, b2, bv_tri (tri_lt _ _)]

theorem testBit_land_of {M K t : Nat} (h : Nat.land M K = M) (hK : K.testBit t = false) :
    M.testBit t = false := by
  rw [← h]
  change (M &&& K).testBit t = false
  rw [Nat.testBit_and, hK, Bool.and_false]

theorem col27_sound {d N M : Nat} {cs : List Char} (hd : 0 < d) (hN : N = d * d)
    (h : run27 d d N M cs 0 = true)
    (hm : Nat.land M (Nat.lor (rep1 d d) (Nat.shiftLeft (rep1 d d) N)) = M) :
    (∀ c ∈ cs, c.toNat < 128) ∧ d ≤ 3 * cs.length ∧
      ∀ i j : Fin d, mat3 d N M i j = if j.val = 0 then (tri cs i.val : ZMod 3) else 0 := by
  obtain ⟨h1, h2, h3⟩ := run27_sound h
  refine ⟨h1, h2, fun i j => ?_⟩
  unfold mat3
  by_cases hj : j.val = 0
  · rw [if_pos hj, hj, Nat.add_zero]
    obtain ⟨b1, b2⟩ := h3 i.val i.isLt
    rw [b1, b2, bv_tri (tri_lt _ _)]
  · rw [if_neg hj]
    have hK : ∀ u, (rep1 d d).testBit (d * i.val + j.val + u * 0) = false := by
      intro u
      rw [Nat.mul_zero, Nat.add_zero]
      cases hb : (rep1 d d).testBit (d * i.val + j.val)
      · rfl
      · obtain ⟨c, -, hc⟩ := (rep1_testBit hd d _).1 hb
        have := j.isLt
        have e := dm_eq3 (d := d) (i := i.val) j.isLt
        rw [hc, Nat.mul_comm, Nat.mul_div_cancel _ hd, Nat.mul_comm, Nat.mul_mod_right] at e
        exact absurd e.2.symm hj
    have hlt : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
    have e1 : M.testBit (d * i.val + j.val) = false := by
      apply testBit_land_of hm
      change ((rep1 d d) ||| (rep1 d d) <<< N).testBit _ = false
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have := hK 0
      rw [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      simp [hlt]
    have e2 : M.testBit (N + (d * i.val + j.val)) = false := by
      apply testBit_land_of hm
      change ((rep1 d d) ||| (rep1 d d) <<< N).testBit _ = false
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have := hK 0
      rw [Nat.mul_zero, Nat.add_zero] at this
      have hz : (rep1 d d).testBit (N + (d * i.val + j.val)) = false := by
        apply Nat.testBit_lt_two_pow
        have := sum_lt3 hd d
        rw [← rep1_eq3 hd] at this
        exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by rw [← hN]; omega))
      rw [hz, Nat.add_sub_cancel_left, this]
      simp
    rw [e1, e2]
    rfl

theorem row27_sound {d N M : Nat} {cs : List Char} (hN : N = d * d)
    (h : run27 1 d N M cs 0 = true)
    (hm : Nat.land M (Nat.lor (2 ^ d - 1) (Nat.shiftLeft (2 ^ d - 1) N)) = M) :
    (∀ c ∈ cs, c.toNat < 128) ∧ d ≤ 3 * cs.length ∧
      ∀ i j : Fin d, mat3 d N M i j = if i.val = 0 then (tri cs j.val : ZMod 3) else 0 := by
  obtain ⟨h1, h2, h3⟩ := run27_sound h
  refine ⟨h1, h2, fun i j => ?_⟩
  unfold mat3
  by_cases hi : i.val = 0
  · rw [if_pos hi, hi, Nat.mul_zero, Nat.zero_add]
    obtain ⟨b1, b2⟩ := h3 j.val j.isLt
    rw [Nat.one_mul] at b1 b2
    rw [b1, b2, bv_tri (tri_lt _ _)]
  · rw [if_neg hi]
    have hge : d ≤ d * i.val + j.val := by
      have := Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero hi)
      omega
    have hlt : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
    have hR : ∀ u, d ≤ u → (2 ^ d - 1 : Nat).testBit u = false := fun u hu =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)
        (Nat.pow_le_pow_right (by norm_num) hu))
    have e1 : M.testBit (d * i.val + j.val) = false := by
      apply testBit_land_of hm
      change ((2 ^ d - 1) ||| (2 ^ d - 1) <<< N).testBit _ = false
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hR _ hge]
      simp [hlt]
    have e2 : M.testBit (N + (d * i.val + j.val)) = false := by
      apply testBit_land_of hm
      change ((2 ^ d - 1) ||| (2 ^ d - 1) <<< N).testBit _ = false
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hR _ (by omega), Nat.add_sub_cancel_left,
        hR _ hge]
      simp
    rw [e1, e2]
    rfl

theorem lo_testBit {N X t : Nat} : (X &&& (2 ^ N - 1)).testBit t = (decide (t < N) && X.testBit t) :=
  lo_bit

theorem add_tbl : ∀ x1 x2 y1 y2 : Bool, (x1 && x2) = false → (y1 && y2) = false →
    ((((x2 || y2) ^^ ((x1 || y2) ^^ (x2 || y1))) && ((x1 || y1) ^^ ((x1 || y2) ^^ (x2 || y1)))) =
      false) ∧
    bv ((x2 || y2) ^^ ((x1 || y2) ^^ (x2 || y1))) ((x1 || y1) ^^ ((x1 || y2) ^^ (x2 || y1))) =
      bv x1 x2 + bv y1 y2 := by
  decide

theorem canon_planes {N X : Nat} (hX : Canon3 N X) :
    X &&& (2 ^ N - 1) < 2 ^ N ∧ X >>> N < 2 ^ N := by
  refine ⟨by rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos N), ?_⟩
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos N)).2 (by rw [← Nat.pow_add]; exact hX.1)

theorem pack_bits {N z1 z2 : Nat} (h1 : z1 < 2 ^ N) (h2 : z2 < 2 ^ N) :
    z1 + (z2 <<< N) < 2 ^ (N + N) ∧
      ∀ t, (z1 + (z2 <<< N)).testBit t = if t < N then z1.testBit t else z2.testBit (t - N) := by
  have e : z1 + (z2 <<< N) = 2 ^ N * z2 + z1 := by rw [Nat.shiftLeft_eq]; ring
  rw [e]
  refine ⟨?_, fun t => Nat.testBit_two_pow_mul_add _ h1 t⟩
  calc 2 ^ N * z2 + z1 < 2 ^ N * z2 + 2 ^ N := by omega
    _ = 2 ^ N * (z2 + 1) := by ring
    _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (N + N) := (Nat.pow_add 2 N N).symm

theorem canon_of_planes {N z1 z2 : Nat} (h1 : z1 < 2 ^ N) (h2 : z2 < 2 ^ N)
    (hd : ∀ t, (z1.testBit t && z2.testBit t) = false) : Canon3 N (z1 + (z2 <<< N)) := by
  obtain ⟨hlt, hb⟩ := pack_bits h1 h2
  refine ⟨hlt, fun t ht => ?_⟩
  rw [hb] at ht ⊢
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  by_cases htN : t < N
  · rw [if_pos htN] at ht
    have := hd t
    rw [ht] at this
    simpa using this
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

theorem mat3_planes {d N z1 z2 : Nat} (hN : N = d * d) (h1 : z1 < 2 ^ N) (h2 : z2 < 2 ^ N)
    (i j : Fin d) :
    mat3 d N (z1 + (z2 <<< N)) i j = bv (z1.testBit (d * i.val + j.val)) (z2.testBit (d * i.val + j.val)) := by
  obtain ⟨-, hb⟩ := pack_bits h1 h2
  have hlt : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
  unfold mat3
  rw [hb, hb, if_pos hlt, if_neg (by omega), Nat.add_sub_cancel_left]

theorem canon_bits {N X : Nat} (hX : Canon3 N X) (t : Nat) :
    ((X &&& (2 ^ N - 1)).testBit t && (X >>> N).testBit t) = false := by
  rw [lo_testBit, Nat.testBit_shiftRight]
  cases h : X.testBit t
  · simp
  · rw [hX.2 t h]
    simp

theorem mat3_eq_bits {d N X : Nat} (hN : N = d * d) (i j : Fin d) :
    mat3 d N X i j = bv ((X &&& (2 ^ N - 1)).testBit (d * i.val + j.val))
      ((X >>> N).testBit (d * i.val + j.val)) := by
  have hlt : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
  unfold mat3
  rw [lo_testBit, Nat.testBit_shiftRight, decide_eq_true hlt, Bool.true_and]

theorem addM3_sound {d N X Y : Nat} (hN : N = d * d) (hX : Canon3 N X) (hY : Canon3 N Y) :
    Canon3 N (addM3 N (2 ^ N - 1) X Y) ∧
      mat3 d N (addM3 N (2 ^ N - 1) X Y) = mat3 d N X + mat3 d N Y := by
  obtain ⟨x1l, x2l⟩ := canon_planes hX
  obtain ⟨y1l, y2l⟩ := canon_planes hY
  set x1 := X &&& (2 ^ N - 1)
  set x2 := X >>> N
  set y1 := Y &&& (2 ^ N - 1)
  set y2 := Y >>> N
  have e : addM3 N (2 ^ N - 1) X Y = ((x2 ||| y2) ^^^ ((x1 ||| y2) ^^^ (x2 ||| y1))) +
      (((x1 ||| y1) ^^^ ((x1 ||| y2) ^^^ (x2 ||| y1))) <<< N) := rfl
  have l1 : (x2 ||| y2) ^^^ ((x1 ||| y2) ^^^ (x2 ||| y1)) < 2 ^ N :=
    Nat.xor_lt_two_pow (Nat.or_lt_two_pow x2l y2l)
      (Nat.xor_lt_two_pow (Nat.or_lt_two_pow x1l y2l) (Nat.or_lt_two_pow x2l y1l))
  have l2 : (x1 ||| y1) ^^^ ((x1 ||| y2) ^^^ (x2 ||| y1)) < 2 ^ N :=
    Nat.xor_lt_two_pow (Nat.or_lt_two_pow x1l y1l)
      (Nat.xor_lt_two_pow (Nat.or_lt_two_pow x1l y2l) (Nat.or_lt_two_pow x2l y1l))
  rw [e]
  refine ⟨canon_of_planes l1 l2 fun t => ?_, ?_⟩
  · simp only [Nat.testBit_xor, Nat.testBit_or]
    exact (add_tbl _ _ _ _ (canon_bits hX t) (canon_bits hY t)).1
  · funext i j
    rw [Matrix.add_apply, mat3_planes hN l1 l2, mat3_eq_bits hN, mat3_eq_bits hN]
    simp only [Nat.testBit_xor, Nat.testBit_or]
    exact (add_tbl _ _ _ _ (canon_bits hX _) (canon_bits hY _)).2

theorem neg_tbl : ∀ x1 x2 : Bool, (x1 && x2) = false → bv x2 x1 = -bv x1 x2 := by decide

theorem negM3_sound {d N X : Nat} (hN : N = d * d) (hX : Canon3 N X) :
    Canon3 N (negM3 N (2 ^ N - 1) X) ∧ mat3 d N (negM3 N (2 ^ N - 1) X) = -mat3 d N X := by
  obtain ⟨x1l, x2l⟩ := canon_planes hX
  have e : negM3 N (2 ^ N - 1) X = (X >>> N) + ((X &&& (2 ^ N - 1)) <<< N) := rfl
  rw [e]
  refine ⟨canon_of_planes x2l x1l fun t => ?_, ?_⟩
  · rw [Bool.and_comm]
    exact canon_bits hX t
  · funext i j
    rw [Matrix.neg_apply, mat3_planes hN x2l x1l, mat3_eq_bits hN]
    exact neg_tbl _ _ (canon_bits hX _)

theorem one_lt {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    ONE < 2 ^ N := by
  obtain ⟨hd, hN, -, -, -, hONE⟩ := consts3_facts hc
  subst hONE
  apply Nat.lt_pow_two_of_testBit
  intro u hu
  cases h : (rep1 (d + 1) d).testBit u
  · rfl
  · obtain ⟨c, hc, rfl⟩ := (rep1_testBit (s := d + 1) (by omega) d _).1 h
    have : (d + 1) * c ≤ (d + 1) * (d - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : (d + 1) * (d - 1) + 1 = d * d := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem neg3_sound {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    Canon3 N (Nat.shiftLeft ONE N) ∧ mat3 d N (Nat.shiftLeft ONE N) = -1 := by
  obtain ⟨-, hN, -, -, -, -⟩ := consts3_facts hc
  obtain ⟨h1, h2⟩ := one3_sound hc
  have hlt := one_lt hc
  have e : negM3 N (2 ^ N - 1) ONE = Nat.shiftLeft ONE N := by
    change (ONE >>> N) + ((ONE &&& (2 ^ N - 1)) <<< N) = ONE <<< N
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt, Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  rw [← e]
  obtain ⟨c1, c2⟩ := negM3_sound (d := d) hN h1
  exact ⟨c1, by rw [c2, h2]⟩

theorem rep1_lt {d : Nat} (hd : 0 < d) : rep1 d d < 2 ^ (d * d) := by
  rw [rep1_eq3 hd]
  exact sum_lt3 hd d

theorem rep1_at {d i j : Nat} (hd : 0 < d) (hi : i < d) (hj : j < d) :
    (rep1 d d).testBit (d * i + j) = decide (j = 0) := by
  apply Bool.eq_iff_iff.2
  rw [rep1_testBit hd, decide_eq_true_iff]
  constructor
  · rintro ⟨c, -, hc⟩
    have e := (dm_eq3 (d := d) (i := i) hj).2
    rw [hc, Nat.mul_mod_right] at e
    exact e.symm
  · rintro rfl
    exact ⟨i, hi, by rw [Nat.add_zero]⟩

theorem colM3_sound {d N X t : Nat} (hd : 0 < d) (hN : N = d * d) (hX : Canon3 N X) (ht : t < d) :
    Canon3 N (colM3 (Nat.lor (rep1 d d) (Nat.shiftLeft (rep1 d d) N)) X t) ∧
      ∀ i j : Fin d, mat3 d N (colM3 (Nat.lor (rep1 d d) (Nat.shiftLeft (rep1 d d) N)) X t) i j =
        if j.val = 0 then mat3 d N X i ⟨t, ht⟩ else 0 := by
  have hr := rep1_lt hd
  rw [← hN] at hr
  have hlo : ∀ u, N ≤ u → (rep1 d d).testBit u = false := fun u hu =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hu))
  have hbit : ∀ u, (colM3 (Nat.lor (rep1 d d) (Nat.shiftLeft (rep1 d d) N)) X t).testBit u =
      (X.testBit (t + u) && ((rep1 d d).testBit u || (decide (N ≤ u) && (rep1 d d).testBit (u - N)))) := by
    intro u
    unfold colM3
    change ((X >>> t) &&& ((rep1 d d) ||| (rep1 d d) <<< N)).testBit u = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hX2 : X < 2 ^ (N + N) := hX.1
  refine ⟨⟨?_, fun u hu => ?_⟩, fun i j => ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro u hu
    rw [hbit, hlo u (by omega), hlo (u - N) (by omega)]
    simp
  · rw [hbit] at hu ⊢
    rw [Bool.and_eq_true] at hu
    obtain ⟨h1, h2⟩ := hu
    by_cases huN : u < N
    · have hr' : (rep1 d d).testBit u = true := by
        have : decide (N ≤ u) = false := by simp; omega
        rw [this] at h2
        simpa using h2
      obtain ⟨c, hc, rfl⟩ := (rep1_testBit hd d u).1 hr'
      have hlt : t + d * c < N := by
        rw [hN]
        have := idx_lt3 hc ht
        omega
      rw [show t + (N + d * c) = N + (t + d * c) by omega, hX.2 _ h1]
      simp
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX2 (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
  · have hlt : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
    unfold mat3
    rw [hbit, hbit, hlo (N + (d * i.val + j.val)) (by omega), Nat.add_sub_cancel_left,
      rep1_at hd i.isLt j.isLt]
    by_cases hj : j.val = 0
    · rw [if_pos hj, hj]
      simp only [decide_true, Bool.and_true, Bool.or_true, Bool.true_or, Nat.add_zero,
        show N ≤ N + d * i.val by omega]
      congr 1
      · rw [Nat.add_comm]
      · rw [show t + (N + d * i.val) = N + (d * i.val + t) by omega]
    · rw [if_neg hj]
      simp [hj, show ¬ N ≤ d * i.val + j.val by omega]
      rfl

theorem spinK_spec {mul : Nat → Nat → Nat} {G0 G1 S CC : Nat} {par lab : Nat → Nat} {lo : Nat} :
    ∀ n, spinK mul G0 G1 S CC par lab lo n = true → ∀ i < n,
      Nat.beq (mul (nIf(Nat.beq (lab (lo + i)) (nat_lit 0), G0, G1)) (colM3 CC S (par (lo + i))))
        (colM3 CC S (lo + i)) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true3 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact spinK_spec n h1 i hi
    · exact h2

end CFSG.KS.ONOut

end
