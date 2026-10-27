module

public import Certificates.Data.Kernel.Spor.ColH
public import CFSG.Certificates.Kernel.YModel.NetSem
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.ColH

open CFSG.KC.Enum CFSG.KC.MonsterConv.Perm CFSG.KC.Benes
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem testBit_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem lane16_eq (c j : Nat) : lane16 c j = c / 2 ^ (16 * j) % 2 ^ 16 := by
  unfold lane16
  change (c >>> (16 * j)) &&& (2 ^ 16 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_lane16 (c j b : Nat) :
    (lane16 c j).testBit b = (decide (b < 16) && c.testBit (16 * j + b)) := by
  rw [lane16_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm b]

theorem lane16_lt (c j : Nat) : lane16 c j < 2 ^ 16 := by
  rw [lane16_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 16)

theorem testBit_recOr (F o : Nat → Nat) : ∀ n q,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft (F u) (o u))) n).testBit q =
      decide (∃ u < n, o u ≤ q ∧ (F u).testBit (q - o u) = true)
  | 0, q => by simp
  | n + 1, q => by
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft (F u) (o u))) n) (Nat.shiftLeft (F n) (o n))).testBit
        q = _
    rw [testBit_lor, testBit_recOr F o n q]
    change (_ || (F n <<< o n).testBit q) = _
    rw [Nat.testBit_shiftLeft]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨h1, h2⟩)
      · exact ⟨u, by omega, h⟩
      · exact ⟨n, by omega, h1, h2⟩
    · rintro ⟨u, hu, h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact Or.inl ⟨u, hu, h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩

theorem testBit_planesAt (F o : Nat → Nat) {W c n : Nat} (ho : ∀ u, o u = W * (u + c))
    (hF : ∀ u < n, F u < 2 ^ W) {v r q : Nat} (hr : r < W) (hq : q = W * (v + c) + r) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft (F u) (o u))) n).testBit q =
      (decide (v < n) && (F v).testBit r) := by
  subst hq
  rw [testBit_recOr]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, h1, h2⟩
    rw [ho] at h1 h2
    rcases Nat.lt_trichotomy u v with h | h | h
    · have e : W * (u + c) + W ≤ W * (v + c) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left W (by omega)
      have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hF u hu)
        (Nat.pow_le_pow_right (by decide) (by omega : W ≤ W * (v + c) + r - W * (u + c))))
      rw [this] at h2
      exact absurd h2 (by decide)
    · subst h
      refine ⟨hu, ?_⟩
      rwa [Nat.add_sub_cancel_left] at h2
    · have e : W * (v + c) + W ≤ W * (u + c) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left W (by omega)
      omega
  · rintro ⟨hv, h⟩
    refine ⟨v, hv, by rw [ho]; omega, ?_⟩
    rw [ho, Nat.add_sub_cancel_left]
    exact h

theorem testBit_planesAt_lo (F o : Nat → Nat) {W c n q : Nat} (ho : ∀ u, o u = W * (u + c))
    (hq : q < W * c) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft (F u) (o u))) n).testBit q = false := by
  rw [testBit_recOr]
  apply decide_eq_false
  rintro ⟨u, -, h1, -⟩
  rw [ho] at h1
  have : W * c ≤ W * (u + c) := Nat.mul_le_mul_left W (by omega)
  omega

theorem testBit_mul65535 : ∀ q y, (∀ i, y.testBit i = true → i % 16 = 0) →
    (y * 65535).testBit q = y.testBit (16 * (q / 16)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro y hy
    have hlo : y % 2 ^ 16 < 2 := by
      apply Nat.lt_pow_two_of_testBit (n := 1)
      intro i hi
      rw [Nat.testBit_mod_two_pow]
      cases h : y.testBit i
      · simp
      · have := hy i h
        simp only [Bool.and_true, decide_eq_false_iff_not, not_lt]
        omega
    have hb : y % 2 ^ 16 * 65535 < 2 ^ 16 := by omega
    have e : y * 65535 = 2 ^ 16 * (y / 2 ^ 16 * 65535) + y % 2 ^ 16 * 65535 := by
      rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.div_add_mod]
    rw [e, Nat.testBit_two_pow_mul_add _ hb]
    split
    · next hq =>
      have e0 : 16 * (q / 16) = 0 := by omega
      rw [e0]
      have h0 : y.testBit 0 = decide (y % 2 ^ 16 = 1) := by
        rw [Nat.testBit_zero]
        congr 1
        apply propext
        omega
      rw [h0]
      rcases (by omega : y % 2 ^ 16 = 0 ∨ y % 2 ^ 16 = 1) with h | h
      · rw [h]; simp
      · rw [h, Nat.one_mul]
        have : (65535 : Nat) = 2 ^ 16 - 1 := rfl
        rw [this, Nat.testBit_two_pow_sub_one]
        simp [hq]
    · next hq =>
      rw [ih (q - 16) (by omega) (y / 2 ^ 16) (fun i hi => by
        rw [Nat.testBit_div_two_pow] at hi
        have := hy _ hi
        omega), Nat.testBit_div_two_pow]
      congr 1
      omega

theorem testBit_repU16 (K i : Nat) :
    (repU 16 K).testBit i = (decide (i < 16 * K) && decide (i % 16 = 0)) := by
  rw [repU_eq, ← Nat.one_mul ((2 ^ (16 * K) - 1) / (2 ^ 16 - 1)),
    testBit_mul_div (by decide) rfl (by decide)]
  congr 1
  rcases Nat.eq_zero_or_pos (i % 16) with h | h
  · rw [h]
    rfl
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
      (Nat.pow_le_pow_right (by decide) h)), decide_eq_false (by omega)]

theorem testBit_repU128 {c : Nat} (hc : c < 2 ^ 128) (K i : Nat) :
    (Nat.mul (repU 128 K) c).testBit i = (decide (i < 128 * K) && c.testBit (i % 128)) := by
  change (repU 128 K * c).testBit i = _
  rw [repU_eq, Nat.mul_comm, testBit_mul_div (by decide) rfl hc]

theorem expP_eq (kL P : Nat) : expP kL P = Nat.lor
    (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft (idPlane (2 ^ (kL + 4)) u) (Nat.mul (2 ^ (kL + 4)) u))) 4)
    (Nat.rec (motive := fun _ => Nat) 0
      (fun u acc => Nat.lor acc (Nat.shiftLeft
        (Nat.mul (Nat.land (Nat.shiftRight P u) (repU 16 (2 ^ kL))) 65535)
        (Nat.mul (2 ^ (kL + 4)) (Nat.add u 4)))) kL) := by
  have h1 : Nat.shiftLeft (nat_lit 1) (Nat.add kL (nat_lit 4)) = 2 ^ (kL + 4) := Nat.one_shiftLeft _
  have h2 : Nat.shiftLeft (nat_lit 1) kL = 2 ^ kL := Nat.one_shiftLeft _
  unfold expP
  rw [h1, h2]
  rfl

theorem testBit_expP {kL P : Nat} {u r : Nat} (hu : u < kL + 4) (hr : r < 2 ^ (kL + 4)) :
    (expP kL P).testBit (2 ^ (kL + 4) * u + r) =
      if u < 4 then r.testBit u else P.testBit (16 * (r / 16) + (u - 4)) := by
  rw [expP_eq, testBit_lor]
  have hB : ∀ v < kL, (Nat.mul (Nat.land (Nat.shiftRight P v) (repU 16 (2 ^ kL))) 65535).testBit r =
      P.testBit (16 * (r / 16) + v) := by
    intro v _
    change ((P >>> v &&& repU 16 (2 ^ kL)) * 65535).testBit r = _
    rw [testBit_mul65535 r _ (fun i hi => by
      rw [Nat.testBit_and, testBit_repU16, Bool.and_eq_true, Bool.and_eq_true] at hi
      exact of_decide_eq_true hi.2.2), Nat.testBit_and, testBit_repU16, Nat.testBit_shiftRight]
    have : 16 * (r / 16) < 16 * 2 ^ kL := by
      have : 2 ^ (kL + 4) = 16 * 2 ^ kL := by rw [Nat.pow_add]; omega
      omega
    simp only [this, decide_true, Nat.mul_mod_right, Bool.and_true]
    rw [Nat.add_comm]
  have hBlt : ∀ v < kL, Nat.mul (Nat.land (Nat.shiftRight P v) (repU 16 (2 ^ kL))) 65535 <
      2 ^ 2 ^ (kL + 4) := by
    intro v _
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    change ((P >>> v &&& repU 16 (2 ^ kL)) * 65535).testBit i = false
    rw [testBit_mul65535 i _ (fun i hi => by
      rw [Nat.testBit_and, testBit_repU16, Bool.and_eq_true, Bool.and_eq_true] at hi
      exact of_decide_eq_true hi.2.2), Nat.testBit_and, testBit_repU16]
    have : 2 ^ (kL + 4) = 16 * 2 ^ kL := by rw [Nat.pow_add]; omega
    have : ¬ 16 * (i / 16) < 16 * 2 ^ kL := by omega
    simp [this]
  have hA : ∀ v < 4, idPlane (2 ^ (kL + 4)) v < 2 ^ 2 ^ (kL + 4) := fun v hv =>
    CFSG.KC.YModel.Sem.idPlane_lt (by omega)
  by_cases h4 : u < 4
  · rw [if_pos h4]
    have e1 := testBit_planesAt (fun v => idPlane (2 ^ (kL + 4)) v)
      (fun v => Nat.mul (2 ^ (kL + 4)) v) (c := 0) (n := 4) (v := u)
      (q := 2 ^ (kL + 4) * u + r)
      (fun v => by rw [Nat.add_zero]; rfl) (fun v hv => hA v hv) hr (by simp only [Nat.add_zero])
    rw [e1, testBit_planesAt_lo _ (fun v => Nat.mul (2 ^ (kL + 4)) (Nat.add v 4)) (c := 4)
      (fun v => rfl) (by
        have : 2 ^ (kL + 4) * u + 2 ^ (kL + 4) ≤ 2 ^ (kL + 4) * 4 := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega), Bool.or_false, decide_eq_true h4, Bool.true_and,
      CFSG.KC.Benes.idPlane_testBit (by omega), decide_eq_true hr, Bool.true_and]
  · rw [if_neg h4]
    have e2 := testBit_planesAt
      (fun v => Nat.mul (Nat.land (Nat.shiftRight P v) (repU 16 (2 ^ kL))) 65535)
      (fun v => Nat.mul (2 ^ (kL + 4)) (Nat.add v 4)) (c := 4) (n := kL) (v := u - 4)
      (q := 2 ^ (kL + 4) * u + r) (fun v => rfl) hBlt hr (by congr 2; omega)
    rw [e2, decide_eq_true (by omega : u - 4 < kL), Bool.true_and, hB _ (by omega)]
    have e1 := testBit_planesAt (fun v => idPlane (2 ^ (kL + 4)) v)
      (fun v => Nat.mul (2 ^ (kL + 4)) v) (c := 0) (n := 4) (v := u)
      (q := 2 ^ (kL + 4) * u + r) (fun v => by rw [Nat.add_zero]; rfl) (fun v hv => hA v hv) hr
      (by simp only [Nat.add_zero])
    rw [e1, decide_eq_false h4, Bool.false_and, Bool.false_or]

theorem pin_spec {kL N P : Nat} (hkL : kL ≤ 16) (h : pinK kL N P = true) :
    StagesValid (kL + 4) N ∧ ∀ r < 2 ^ (kL + 4),
      benesPerm (kL + 4) N r = 16 * (lane16 P (r / 16) % 2 ^ kL) + r % 16 := by
  unfold pinK at h
  beta_reduce at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hv : StagesValid (kL + 4) N := stagesValid_of_netValid h1
  refine ⟨hv, fun r hr => ?_⟩
  have e : netApply (kL + 4) (1 <<< (kL + 4)) (repU (1 <<< (kL + 4)) (kL + 4)) N (idP (kL + 4)) =
      expP kL P := Nat.eq_of_beq_eq_true h2
  rw [Nat.one_shiftLeft] at e
  have hn := testBit_netApply (k := kL + 4) (P := kL + 4) rfl hv (idP (kL + 4))
  have hpl : 2 ^ (kL + 4) = 16 * 2 ^ kL := by rw [Nat.pow_add]; omega
  have hlt : 16 * (lane16 P (r / 16) % 2 ^ kL) + r % 16 < 2 ^ (kL + 4) := by
    have := Nat.mod_lt (lane16 P (r / 16)) (Nat.two_pow_pos kL)
    omega
  apply Nat.eq_of_testBit_eq
  intro u
  by_cases hu : u < kL + 4
  · have a := hn.1 u hu r hr
    rw [CFSG.KC.YModel.Sem.testBit_idP hu (benesPerm_lt hv hr), e, testBit_expP hu hr] at a
    rw [← a]
    have e16 : 16 * (lane16 P (r / 16) % 2 ^ kL) + r % 16 =
        2 ^ 4 * (lane16 P (r / 16) % 2 ^ kL) + r % 2 ^ 4 := rfl
    rw [e16, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos 4))]
    split
    · next h4 =>
      rw [Nat.testBit_mod_two_pow, decide_eq_true h4, Bool.true_and]
    · next h4 =>
      rw [Nat.testBit_mod_two_pow, testBit_lane16, decide_eq_true (by omega : u - 4 < kL),
        decide_eq_true (by omega : u - 4 < 16), Bool.true_and, Bool.true_and]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (benesPerm_lt hv hr)
      (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem col_lane {kL N P : Nat} (hkL : kL ≤ 16) (h : pinK kL N P = true) (X : Nat) {j : Nat}
    (hj : j < 2 ^ kL) :
    lane16 (netApply (kL + 4) (Nat.shiftLeft 1 (kL + 4)) 1 N X) j = lane16 X (lane16 P j % 2 ^ kL) := by
  obtain ⟨hv, hp⟩ := pin_spec hkL h
  change lane16 (netApply (kL + 4) (1 <<< (kL + 4)) 1 N X) j = _
  have hpl : 2 ^ (kL + 4) = 16 * 2 ^ kL := by rw [Nat.pow_add]; omega
  have hn := testBit_netApply (k := kL + 4) (P := 1) (Nat.one_shiftLeft _) hv X
  rw [repU_one (by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos _)] at hn
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_lane16, testBit_lane16]
  by_cases hb : b < 16
  · rw [decide_eq_true hb, Bool.true_and, Bool.true_and]
    have a := hn.1 0 (by omega) (16 * j + b) (by rw [Nat.one_shiftLeft]; omega)
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, hp _ (by omega)] at a
    rw [a, show (16 * j + b) / 16 = j by omega, show (16 * j + b) % 16 = b by omega]
  · rw [decide_eq_false hb, Bool.false_and, Bool.false_and]

theorem colSlK_spec {k N w m G : Nat} {C : Nat → Nat} {lo : Nat} : ∀ {len : Nat},
    colSlK k N w m G C lo len = true → ∀ i, lo ≤ i → i < lo + len →
      netApply k (Nat.shiftLeft 1 k) 1 N (C (pg w m G i)) = C i
  | 0, _, i, h1, h2 => absurd h2 (by omega)
  | len + 1, h, i, h1, h2 => by
    have h' : strictB (Nat.add lo len) (fun i => bAnd(
        Nat.beq (netApply k (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1) N (C (pg w m G i))) (C i),
        colSlK k N w m G C lo len)) = true := h
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge i (lo + len) with hi | hi
    · exact colSlK_spec h'.2 i h1 hi
    · have e : i = lo + len := by omega
      subst e
      exact Nat.eq_of_beq_eq_true h'.1

@[expose] def ln (X q : Nat) : Nat := X / 2 ^ (128 * q) % 2 ^ 128

theorem testBit_ln (X q i : Nat) : (ln X q).testBit i = (decide (i < 128) && X.testBit (128 * q + i)) := by
  unfold ln
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]

theorem ln_xor (X Y q : Nat) : ln (X ^^^ Y) q = ln X q ^^^ ln Y q :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_ln, Nat.testBit_xor]
    cases decide (i < 128) <;> simp

theorem ln_and (X Y q : Nat) : ln (X &&& Y) q = ln X q &&& ln Y q :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_ln, Nat.testBit_and]
    cases decide (i < 128) <;> simp

theorem ln_zero (X : Nat) : ln X 0 = X % 2 ^ 128 := by simp [ln]

theorem ln_succ (X q : Nat) : ln X (q + 1) = ln (X / 2 ^ 128) q := by
  unfold ln
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

theorem ln_mul {p : Nat} : ∀ q X, (∀ q, ln X q * p < 2 ^ 128) → ln (X * p) q = ln X q * p := by
  intro q
  induction q with
  | zero =>
    intro X hX
    have h0 := hX 0
    rw [ln_zero] at h0 ⊢
    rw [ln_zero]
    have e : X * p = X % 2 ^ 128 * p + 2 ^ 128 * (X / 2 ^ 128 * p) := by
      conv_lhs => rw [← Nat.div_add_mod X (2 ^ 128)]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | succ q ih =>
    intro X hX
    have h0 := hX 0
    rw [ln_zero] at h0
    have e : X * p = X % 2 ^ 128 * p + 2 ^ 128 * (X / 2 ^ 128 * p) := by
      conv_lhs => rw [← Nat.div_add_mod X (2 ^ 128)]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]
    have ed : X * p / 2 ^ 128 = X / 2 ^ 128 * p := by
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 128), Nat.div_eq_of_lt h0, Nat.zero_add]
    rw [ln_succ, ed, ih (X / 2 ^ 128) (fun q => by rw [← ln_succ]; exact hX (q + 1)), ln_succ]

theorem ln_repU {c : Nat} (hc : c < 2 ^ 128) (K q : Nat) :
    ln (Nat.mul (repU 128 K) c) q = if q < K then c else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ln, testBit_repU128 hc]
  by_cases hi : i < 128
  · rw [decide_eq_true hi, Bool.true_and, show (128 * q + i) % 128 = i by omega]
    split
    · next h => rw [decide_eq_true (by omega)]; rfl
    · next h => rw [decide_eq_false (by omega)]; simp
  · rw [decide_eq_false hi, Bool.false_and]
    split
    · exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (by decide) (by omega)))).symm
    · simp

theorem testBit_spM (M i : Nat) : (spM M).testBit i = (decide (i < 128 * M) && decide (i % 128 < 16)) := by
  unfold spM
  rw [testBit_repU128 (by decide)]
  congr 1
  change (2 ^ 16 - 1).testBit (i % 128) = _
  rw [Nat.testBit_two_pow_sub_one]

theorem vec_plane_lt (M c r : Nat) :
    Nat.land (Nat.shiftRight c (Nat.mul 16 r)) (spM M) < 2 ^ (128 * M) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  change (c >>> (16 * r) &&& spM M).testBit i = false
  rw [Nat.testBit_and, testBit_spM, decide_eq_false (by omega)]
  simp

theorem vecK_eq (M c : Nat) : vecK M c = Nat.rec (motive := fun _ => Nat) 0
    (fun u acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight c (Nat.mul 16 u)) (spM M))
      (Nat.mul (Nat.mul 128 M) u))) 8 := rfl

theorem ln_vecK {M c r m : Nat} (hr : r < 8) (hm : m < M) :
    ln (vecK M c) (M * r + m) = lane16 c (8 * m + r) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ln, testBit_lane16]
  by_cases hi : i < 128
  · rw [decide_eq_true hi, Bool.true_and]
    have e : 128 * (M * r + m) + i = (128 * M) * (r + 0) + (128 * m + i) := by
      rw [Nat.add_zero, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
    have hlt : 128 * m + i < 128 * M := by
      have : 128 * m + 128 ≤ 128 * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hm
      omega
    rw [vecK_eq, testBit_planesAt (fun r => Nat.land (Nat.shiftRight c (Nat.mul 16 r)) (spM M))
      (fun r => Nat.mul (Nat.mul 128 M) r) (c := 0) (n := 8) (v := r)
      (fun u => by rw [Nat.add_zero]; rfl) (fun u _ => vec_plane_lt M c u) hlt e,
      decide_eq_true hr, Bool.true_and]
    change (c >>> (16 * r) &&& spM M).testBit (128 * m + i) = _
    rw [Nat.testBit_and, testBit_spM, Nat.testBit_shiftRight, decide_eq_true hlt, Bool.true_and,
      show (128 * m + i) % 128 = i by omega]
    have e2 : 16 * r + (128 * m + i) = 16 * (8 * m + r) + i := by omega
    by_cases h16 : i < 16 <;> simp [h16, e2]
  · rw [decide_eq_false hi, Bool.false_and, decide_eq_false (by omega), Bool.false_and]

theorem ln_vecK_lt (M c q : Nat) : ln (vecK M c) q < 2 ^ 16 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_ln]
  by_cases h : i < 128
  · rw [decide_eq_true h, Bool.true_and]
    rw [vecK_eq, testBit_recOr]
    apply decide_eq_false
    rintro ⟨u, hu, h1, h2⟩
    change (c >>> (16 * u) &&& spM M).testBit _ = true at h2
    rw [Nat.testBit_and, testBit_spM, Bool.and_eq_true, Bool.and_eq_true] at h2
    have h3 := of_decide_eq_true h2.2.2
    have ho : Nat.mul (Nat.mul 128 M) u = 128 * (M * u) := by
      change 128 * M * u = _
      rw [Nat.mul_assoc]
    rw [ho] at h1 h3
    generalize M * u = X at h1 h3
    omega
  · rw [decide_eq_false h, Bool.false_and]

@[expose] noncomputable def stepH (M : Nat) (C : Nat → Nat) (L i h : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.xor h (vecK M (C i))) (nat_lit 1099511628211)) L

theorem hgoK_succ (M : Nat) (C : Nat → Nat) (L rem i h : Nat) :
    hgoK M C L (rem + 1) i h = hgoK M C L rem (i + 1) (stepH M C L i h) :=
  strictN_eq (stepH M C L i h) (fun h' => hgoK M C L rem (i + 1) h')

theorem hgoK_last (M : Nat) (C : Nat → Nat) (L : Nat) : ∀ rem i h,
    hgoK M C L (rem + 1) i h = stepH M C L (i + rem) (hgoK M C L rem i h)
  | 0, i, h => by rw [hgoK_succ]; rfl
  | rem + 1, i, h => by
    rw [hgoK_succ, hgoK_last M C L rem (i + 1), hgoK_succ, Nat.add_right_comm, Nat.add_assoc]

@[expose] noncomputable def colT (n : Nat) (C : Nat → Nat) (j : Nat) : Table :=
  CFSG.KS.MulH.tabT (Array.ofFn (n := n) fun i => lane16 (C i.val) j)

theorem colT_size (n : Nat) (C : Nat → Nat) (j : Nat) : (colT n C j).size = n := by
  simp [colT, CFSG.KS.MulH.tabT]

theorem colT_get {n : Nat} {C : Nat → Nat} {j i : Nat} (hi : i < n) :
    (colT n C j)[i]! = UInt32.ofNat (lane16 (C i) j) := by
  unfold colT
  rw [CFSG.KS.MulH.tabT_get, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem colT_toNat {n : Nat} {C : Nat → Nat} {j i : Nat} (hi : i < n) :
    ((colT n C j)[i]!).toNat = lane16 (C i) j := by
  rw [colT_get hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (lane16_lt _ _)
    (Nat.pow_le_pow_right (by decide) (by decide)))]

@[expose] def Small (X : Nat) : Prop := ∀ q, ln X q < 2 ^ 64

@[expose] def qf (M j : Nat) : Nat := M * (j % 8) + j / 8

theorem hashColK_lanes {M n : Nat} (C : Nat → Nat) : ∀ r ≤ n,
    Small (hgoK M C (lowK M) r 0 (offK M)) ∧ ∀ j < 8 * M,
      ln (hgoK M C (lowK M) r 0 (offK M)) (qf M j) =
        (Nat.fold r (fun i _ h => (h ^^^ ((colT n C j)[i]!).toUInt64) * 1099511628211)
          (14695981039346656037 : UInt64)).toNat := by
  have hL : ∀ q, ln (lowK M) q = if q < 8 * M then 2 ^ 64 - 1 else 0 := fun q =>
    ln_repU (by decide) _ q
  have hO : ∀ q, ln (offK M) q = if q < 8 * M then 14695981039346656037 else 0 := fun q =>
    ln_repU (by decide) _ q
  have hq : ∀ j < 8 * M, qf M j < 8 * M := by
    intro j hj
    unfold qf
    have : M * (j % 8) + M ≤ M * 8 := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have : j / 8 < M := by omega
    omega
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun q => ?_, fun j hj => ?_⟩
    · change ln (offK M) q < _
      rw [hO]
      split <;> omega
    · change ln (offK M) _ = _
      rw [hO, if_pos (hq j hj), Nat.fold_zero]
      rfl
  | succ r ih =>
    intro hr
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [hgoK_last, Nat.zero_add]
    generalize hgoK M C (lowK M) r 0 (offK M) = S at hs hv
    have hx : ∀ q, ln (S ^^^ vecK M (C r)) q < 2 ^ 64 := fun q => by
      rw [ln_xor]
      exact Nat.xor_lt_two_pow (hs q) (Nat.lt_of_lt_of_le (ln_vecK_lt M _ q)
        (Nat.pow_le_pow_right (by decide) (by decide)))
    have hstep : ∀ q, ln (stepH M C (lowK M) r S) q =
        if q < 8 * M then (ln S q ^^^ ln (vecK M (C r)) q) * 1099511628211 % 2 ^ 64 else 0 := by
      intro q
      unfold stepH
      change ln ((S ^^^ vecK M (C r)) * 1099511628211 &&& lowK M) q = _
      rw [ln_and, ln_mul q _ (fun q => by have := hx q; omega), hL, ln_xor]
      split
      · rw [Nat.and_two_pow_sub_one_eq_mod]
      · simp
    refine ⟨fun q => ?_, fun j hj => ?_⟩
    · rw [hstep]
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos 64)
      · exact Nat.two_pow_pos 64
    · rw [hstep, if_pos (hq j hj), Nat.fold_succ, hv j hj, UInt64.toNat_mul, UInt64.toNat_xor,
        UInt32.toNat_toUInt64, colT_toNat (by omega)]
      have e : ln (vecK M (C r)) (qf M j) = lane16 (C r) j := by
        unfold qf
        rw [ln_vecK (by omega) (by omega)]
        congr 1
        omega
      rw [e]
      rfl

theorem hkey_colT {M n : Nat} (C : Nat → Nat) {j : Nat} (hj : j < 8 * M) :
    laneH M (hashColK M n C) j = (hkey n (colT n C j)).toNat := by
  have h := hashColK_lanes (M := M) (n := n) C n (Nat.le_refl n)
  have e : hashColK M n C = hgoK M C (lowK M) n 0 (offK M) :=
    strictN_eq (lowK M) (fun L => hgoK M C L n 0 (offK M))
  have h2 : ln (hgoK M C (lowK M) n 0 (offK M)) (qf M j) = (hkey n (colT n C j)).toNat :=
    h.2 j hj
  have hs := h.1 (qf M j)
  rw [e, ← h2]
  unfold laneH
  change hgoK M C (lowK M) n 0 (offK M) >>> (128 * qf M j) &&& (2 ^ 64 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, ← Nat.mod_eq_of_lt hs]
  unfold ln
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 64 ≤ 128))]

theorem laneH_inj {M H cnt HS HSI : Nat} (h : allN cnt (hsortK M H cnt HS HSI) = true) :
    ∀ a < cnt, ∀ b < cnt, laneH M H a = laneH M H b → a = b := by
  refine CFSG.KS.MulH.inj_of_sortH (T := laneH M H) (S := lane16 HS) (SI := lane16 HSI)
    fun i hi => ?_
  have h' := CFSG.KS.allN_spec h i hi
  unfold hsortK at h'
  rw [strictB_eq, bAnd_eq, bAnd_eq, bIf_eq] at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
  rw [if_pos (Nat.blt_eq.mpr hc)] at h3
  exact Nat.blt_eq.mp h3

theorem surj_of_inj {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < n)
    (hinj : ∀ a < n, ∀ b < n, f a = f b → a = b) : ∀ j < n, ∃ i < n, f i = j := by
  classical
  have himg : (Finset.range n).image f = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hf i (Finset.mem_range.1 hi))
    · rw [Finset.card_image_of_injOn fun a ha b hb e =>
        hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e]
  intro j hj
  have : j ∈ (Finset.range n).image f := by rw [himg]; exact Finset.mem_range.2 hj
  obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
  exact ⟨i, Finset.mem_range.1 hi, e⟩

theorem idxK_spec {cnt PAR LAB POS : Nat} {PI : Nat → Nat} {i : Nat}
    (h : idxK cnt PAR LAB POS PI i = true) :
    (i = 0 → lane16 PAR 0 = 0 ∧ lane16 LAB 0 = 0) ∧
    (0 < i → lane16 PAR i < i ∧ lane16 LAB i < 2 ∧
      lane16 POS (2 * lane16 PAR i + lane16 LAB i) = i ∧
      (i + 1 < cnt → CFSG.KS.BfsReplay.LexLt (lane16 PAR i) (lane16 LAB i) (lane16 PAR (i + 1))
        (lane16 LAB (i + 1)))) ∧
    (∀ l < 2, lane16 POS (2 * i + l) < cnt ∧ lane16 (PI l) (lane16 POS (2 * i + l)) = i ∧
      (lane16 POS (2 * i + l) = 0 ∨ ¬ CFSG.KS.BfsReplay.LexLt i l
        (lane16 PAR (lane16 POS (2 * i + l))) (lane16 LAB (lane16 POS (2 * i + l))))) := by
  unfold idxK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun l hl => ?_⟩
  · subst h0
    rw [bIf_eq, if_pos (Nat.beq_refl 0), Bool.and_eq_true] at hA
    exact ⟨Nat.eq_of_beq_eq_true hA.1, Nat.eq_of_beq_eq_true hA.2⟩
  · rw [bIf_eq, if_neg (by rw [Nat.beq_eq]; omega)] at hA
    simp only [bAnd_eq, Bool.and_eq_true] at hA
    obtain ⟨a1, a2, a3, a4⟩ := hA
    refine ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3, fun hc => ?_⟩
    rw [bIf_eq, if_pos (Nat.blt_eq.mpr hc), bIf_eq] at a4
    unfold CFSG.KS.BfsReplay.LexLt
    by_cases h5 : Nat.blt (lane16 PAR i) (lane16 PAR (Nat.succ i)) = true
    · exact Or.inl (Nat.blt_eq.mp h5)
    · rw [if_neg h5, Bool.and_eq_true] at a4
      exact Or.inr ⟨Nat.eq_of_beq_eq_true a4.1, Nat.blt_eq.mp a4.2⟩
  · have hb := CFSG.KS.allN_spec hB l hl
    rw [strictB_eq] at hb
    simp only [bAnd_eq, Bool.and_eq_true] at hb
    have e2 : Nat.add (Nat.mul 2 i) l = 2 * i + l := rfl
    rw [e2] at hb
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨Nat.blt_eq.mp b1, Nat.eq_of_beq_eq_true b2, ?_⟩
    rw [bIf_eq] at b3
    generalize lane16 POS (2 * i + l) = q at b3 ⊢
    by_cases h0 : Nat.beq q 0 = true
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · right
      rw [if_neg h0, bIf_eq] at b3
      unfold CFSG.KS.BfsReplay.LexLt
      generalize lane16 PAR q = p at b3 ⊢
      generalize lane16 LAB q = b at b3 ⊢
      by_cases h1 : Nat.blt i p = true
      · rw [if_pos h1] at b3
        exact absurd b3 (by decide)
      · rw [if_neg h1, bIf_eq] at b3
        have h1' : ¬ i < p := fun hlt => h1 (Nat.blt_eq.mpr hlt)
        by_cases h2 : Nat.beq i p = true
        · rw [if_pos h2] at b3
          have := Nat.le_of_ble_eq_true b3
          omega
        · have h2' : ¬ i = p := fun e => h2 (by rw [Nat.beq_eq]; exact e)
          omega

section Replay

variable {M n cnt kL : Nat} {C : Nat → Nat} {N PI : Nat → Nat} {G : Nat → Nat → Nat}

theorem col_step (hkL : kL ≤ 16) (hpin : ∀ l < 2, pinK kL (N l) (PI l) = true)
    (hcol : ∀ l < 2, ∀ i < n,
      netApply (kL + 4) (Nat.shiftLeft 1 (kL + 4)) 1 (N l) (C (G l i)) = C i)
    {g : Table} {l q j : Nat} (hl : l < 2) (hg : ∀ i < n, (g[i]!).toNat = G l i ∧ G l i < n)
    (hj : j < 2 ^ kL) (hq : lane16 (PI l) j % 2 ^ kL = q) :
    compT n (colT n C q) g = colT n C j := by
  apply Array.ext (by rw [colT_size]; simp [compT])
  intro i h1 _
  have hi : i < n := by simpa [compT] using h1
  rw [← getElem!_pos (colT n C j) i (by rw [colT_size]; exact hi), colT_get hi]
  simp only [compT, Array.getElem_ofFn]
  rw [(hg i hi).1, colT_get (hg i hi).2, ← hcol l hl i hi, col_lane hkL (hpin l hl) _ hj, hq]

theorem col_inv (hkL : kL ≤ 16) (hpin : ∀ l < 2, pinK kL (N l) (PI l) = true)
    (hcol : ∀ l < 2, ∀ i < n,
      netApply (kL + 4) (Nat.shiftLeft 1 (kL + 4)) 1 (N l) (C (G l i)) = C i)
    {g : Table} {I : Nat → Nat} {l q : Nat} (hl : l < 2)
    (hg : ∀ i < n, (g[i]!).toNat = I i ∧ I i < n ∧ G l (I i) = i) (hq : q < 2 ^ kL) :
    compT n (colT n C q) g = colT n C (lane16 (PI l) q % 2 ^ kL) := by
  apply Array.ext (by rw [colT_size]; simp [compT])
  intro i h1 _
  have hi : i < n := by simpa [compT] using h1
  rw [← getElem!_pos (colT n C _) i (by rw [colT_size]; exact hi), colT_get hi]
  simp only [compT, Array.getElem_ofFn]
  obtain ⟨g1, g2, g3⟩ := hg i hi
  rw [g1, colT_get g2, ← hcol l hl (I i) g2, col_lane hkL (hpin l hl) _ hq, g3]

theorem pi_lt {cnt PAR LAB POS : Nat} {PI : Nat → Nat} (hidx : allN cnt (idxK cnt PAR LAB POS PI) = true)
    {l : Nat} (hl : l < 2) : ∀ q < cnt, lane16 (PI l) q < cnt := by
  have hs := fun i hi => (idxK_spec (CFSG.KS.allN_spec hidx i hi)).2.2 l hl
  intro q hq
  obtain ⟨i, hi, e⟩ := surj_of_inj (n := cnt) (f := fun i => lane16 POS (2 * i + l))
    (fun i hi => (hs i hi).1)
    (fun a ha b hb e => by rw [← (hs a ha).2.1, ← (hs b hb).2.1]; exact congrArg _ e) q hq
  rw [← e, (hs i hi).2.1]
  exact hi

theorem colT_root (hroot : rootK C n = true) : colT n C 0 = idT n := by
  apply Array.ext (by rw [colT_size]; simp [idT])
  intro i h1 _
  have hi : i < n := by rwa [colT_size] at h1
  rw [← getElem!_pos (colT n C 0) i h1, colT_get hi]
  simp only [idT, Array.getElem_ofFn]
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hroot i hi)]

theorem col_replay {PAR LAB POS HS HSI : Nat} {gens : Array Table}
    (hkL : kL ≤ 16) (hpos : 0 < cnt) (hcnt : cnt ≤ 2 ^ kL) (hcnt8 : cnt ≤ 8 * M)
    (hpin : ∀ l < 2, pinK kL (N l) (PI l) = true)
    (hcol : ∀ l < 2, ∀ i < n,
      netApply (kL + 4) (Nat.shiftLeft 1 (kL + 4)) 1 (N l) (C (G l i)) = C i)
    (hgs : gens.size = 2) (hg : ∀ l < 2, ∀ i < n, ((gens[l]!)[i]!).toNat = G l i ∧ G l i < n)
    (hidx : allN cnt (idxK cnt PAR LAB POS PI) = true) (hroot : rootK C n = true)
    (hsort : allN cnt (hsortK M (hashColK M n C) cnt HS HSI) = true) :
    CFSG.KS.HBfs.HReplay (hkey n) (fun j y => compT n y gens[j]!) gens.size (idT n) cnt (colT n C)
      (lane16 PAR) (lane16 LAB) (fun h l => lane16 POS (2 * h + l)) := by
  have hs := fun i hi => idxK_spec (CFSG.KS.allN_spec hidx i hi)
  have hclose : ∀ h < cnt, ∀ l < 2, compT n (colT n C h) gens[l]! =
      colT n C (lane16 POS (2 * h + l)) := by
    intro h hh l hl
    obtain ⟨c1, c2, -⟩ := (hs h hh).2.2 l hl
    exact col_step hkL hpin hcol hl (hg l hl) (by omega) (by rw [c2]; exact Nat.mod_eq_of_lt (by omega))
  rw [hgs]
  refine ⟨hpos, colT_root hroot, ((hs 0 hpos).1 rfl).1, ((hs 0 hpos).1 rfl).2,
    fun a ha b hb e => ?_, fun i h0 hi => ?_, fun i h0 hi => ((hs i (by omega)).2.1 h0).2.2.2 hi,
    fun h hh l hl => ?_⟩
  · refine laneH_inj hsort a ha b hb ?_
    rw [hkey_colT C (by omega), hkey_colT C (by omega), e]
  · obtain ⟨t1, t2, t3, -⟩ := (hs i hi).2.1 h0
    refine ⟨t1, t2, ?_⟩
    rw [hclose _ (by omega) _ t2, t3]
  · obtain ⟨c1, -, c3⟩ := (hs h hh).2.2 l hl
    exact ⟨c1, (hclose h hh l hl), c3⟩

end Replay

end CFSG.KS.ColH

end
