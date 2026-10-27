module

public import Certificates.Data.Kernel.KDense.Sep
public import CFSG.Certificates.Kernel.KDense.Sound
public import CFSG.Certificates.Kernel.BenesSound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KDense.P15

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes

@[expose] def dg (S x p : ℕ) : ℕ :=
  (x.testBit p).toNat + 2 * (x.testBit (S + p)).toNat + 4 * (x.testBit (2 * S + p)).toNat +
    8 * (x.testBit (3 * S + p)).toNat

theorem resP_dg (S x p : ℕ) : resP S x p = (dg S x p : ZMod 15) := by
  unfold resP dg
  simp only [Nat.toNat_testBit]

theorem testBit_four (a0 a1 a2 a3 : Bool) (i : ℕ) :
    (a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat).testBit i =
      (if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3
        else false) := by
  rcases i with _ | _ | _ | _ | i
  · cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> rfl
  · cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> rfl
  · cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> rfl
  · cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    apply Nat.testBit_lt_two_pow
    have h : a0.toNat + 2 * a1.toNat + 4 * a2.toNat + 8 * a3.toNat < 16 := by
      cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide
    exact lt_of_lt_of_le h (by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 4 ≤ i + 1 + 1 + 1 + 1)
      simpa using this)

theorem testBit_dg (S x p i : ℕ) :
    (dg S x p).testBit i = (decide (i < 4) && x.testBit (i * S + p)) := by
  unfold dg
  rw [testBit_four]
  rcases i with _ | _ | _ | _ | i
  · simp
  · simp
  · simp
  · simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      decide_eq_false (by omega : ¬ i + 1 + 1 + 1 + 1 < 4), Bool.false_and]

theorem dg_lt (S x p : ℕ) : dg S x p < 16 := by
  unfold dg
  cases x.testBit p <;> cases x.testBit (S + p) <;> cases x.testBit (2 * S + p) <;>
    cases x.testBit (3 * S + p) <;> decide

theorem dg_ext {a b : ℕ} (ha : a < 16) (hb : b < 16) (h : ∀ i < 4, a.testBit i = b.testBit i) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 4
  · exact h i hi
  · have h16 : (16 : ℕ) ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 4 ≤ i)
      simpa using this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h16), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h16)]

theorem dg_xor (S x y p : ℕ) : dg S (Nat.xor x y) p = Nat.xor (dg S x p) (dg S y p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dg, nxor, nxor, Nat.testBit_xor, Nat.testBit_xor, testBit_dg, testBit_dg]
  cases decide (i < 4) <;> simp

theorem dg_and (S x y p : ℕ) : dg S (Nat.land x y) p = Nat.land (dg S x p) (dg S y p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dg, nland, nland, Nat.testBit_and, Nat.testBit_and, testBit_dg, testBit_dg]
  cases decide (i < 4) <;> simp

theorem dg_or (S x y p : ℕ) : dg S (Nat.lor x y) p = Nat.lor (dg S x p) (dg S y p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_dg, nlor, nlor, Nat.testBit_or, Nat.testBit_or, testBit_dg, testBit_dg]
  cases decide (i < 4) <;> simp

theorem m4_eq (S : ℕ) : m4 S = 2 ^ (4 * S) - 1 := by
  unfold m4
  rw [Benes.ones_eq, nshl, Nat.shiftLeft_eq, Nat.mul_comm]

theorem rotk_lt (S k x : ℕ) : rotk S k x < 2 ^ (4 * S) := by
  unfold rotk
  rw [m4_eq, nland]
  exact Benes.land_ones_lt _ _

theorem testBit_rotk {S k x : ℕ} (hk : k ≤ 4) (hx : x < 2 ^ (4 * S)) {b p : ℕ} (hb : b < 4)
    (hp : p < S) : (rotk S k x).testBit (b * S + p) = x.testBit (((b + 4 - k) % 4) * S + p) := by
  have hz : ∀ i, 4 * S ≤ i → x.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
  unfold rotk
  rw [m4_eq]
  simp only [nland, nlor, nshl, nshr, nmul, nsub, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  interval_cases b <;> interval_cases k <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, hz, Bool.and_true, Bool.true_and,
      Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMod, Nat.zero_mul, Nat.zero_add, Nat.one_mul] <;>
    congr 1 <;> omega

theorem dg_rotk {S k x p : ℕ} (hk : k ≤ 4) (hx : x < 2 ^ (4 * S)) (hp : p < S) :
    dg S (rotk S k x) p = rotk 1 k (dg S x p) := by
  have hd : dg S x p < 2 ^ (4 * 1) := dg_lt S x p
  have hr : rotk 1 k (dg S x p) < 16 := rotk_lt 1 k _
  refine dg_ext (dg_lt _ _ _) hr fun i hi => ?_
  rw [testBit_dg, decide_eq_true hi, Bool.true_and, testBit_rotk hk hx hi hp]
  have := testBit_rotk (S := 1) (p := 0) hk hd hi Nat.zero_lt_one
  simp only [Nat.mul_one, Nat.add_zero] at this
  rw [this, testBit_dg]
  simp [Nat.mod_lt _ (by decide : 0 < 4)]

theorem lt4_xor {S x y : ℕ} (hx : x < 2 ^ (4 * S)) (hy : y < 2 ^ (4 * S)) :
    Nat.xor x y < 2 ^ (4 * S) := Nat.xor_lt_two_pow hx hy

theorem lt4_and {S x y : ℕ} (hx : x < 2 ^ (4 * S)) : Nat.land x y < 2 ^ (4 * S) :=
  lt_of_le_of_lt Nat.and_le_left hx

theorem lt4_or {S x y : ℕ} (hx : x < 2 ^ (4 * S)) (hy : y < 2 ^ (4 * S)) :
    Nat.lor x y < 2 ^ (4 * S) := Nat.or_lt_two_pow hx hy

theorem add15_lt {S x y : ℕ} (hx : x < 2 ^ (4 * S)) (hy : y < 2 ^ (4 * S)) :
    add15 S x y < 2 ^ (4 * S) :=
  lt4_xor (lt4_xor hx hy) (rotk_lt _ _ _)

theorem dg_add15 {S x y p : ℕ} (hx : x < 2 ^ (4 * S)) (hy : y < 2 ^ (4 * S)) (hp : p < S) :
    dg S (add15 S x y) p = add15 1 (dg S x p) (dg S y p) := by
  have h1 : (1 : ℕ) ≤ 4 := by decide
  have h2 : (2 : ℕ) ≤ 4 := by decide
  have bP := lt4_xor hx hy
  have bG := lt4_and (y := y) hx
  have bG1 := lt4_or bG (lt4_and (y := rotk S 1 (Nat.land x y)) bP)
  have bP1 := lt4_and (y := rotk S 1 (Nat.xor x y)) bP
  have bG2 := lt4_or bG1 (lt4_and (y := rotk S 2 (Nat.lor (Nat.land x y)
    (Nat.land (Nat.xor x y) (rotk S 1 (Nat.land x y))))) bP1)
  unfold add15
  simp (disch := assumption) only [dg_xor, dg_and, dg_or, dg_rotk h1, dg_rotk h2]

theorem add15_one_mod : ∀ a < 16, ∀ c < 16, add15 1 a c % 15 = (a + c) % 15 := by
  decide +kernel

theorem resP_add15 {S x y p : ℕ} (hx : x < 2 ^ (4 * S)) (hy : y < 2 ^ (4 * S)) (hp : p < S) :
    resP S (add15 S x y) p = resP S x p + resP S y p := by
  rw [resP_dg, resP_dg, resP_dg, dg_add15 hx hy hp, ← ZMod.natCast_mod,
    add15_one_mod _ (dg_lt S x p) _ (dg_lt S y p), ZMod.natCast_mod, Nat.cast_add]

theorem rotk_one_mod : ∀ a < 16, ∀ b < 4, rotk 1 b a % 15 = (2 ^ b * a) % 15 := by
  decide +kernel

theorem resP_rotk {S b x p : ℕ} (hb : b < 4) (hx : x < 2 ^ (4 * S)) (hp : p < S) :
    resP S (rotk S b x) p = 2 ^ b * resP S x p := by
  rw [resP_dg, resP_dg, dg_rotk (by omega) hx hp, ← ZMod.natCast_mod,
    rotk_one_mod _ (dg_lt S x p) _ hb, ZMod.natCast_mod]
  push_cast
  rfl

theorem resP_zero' (S p : ℕ) : resP S 0 p = 0 := by simp [resP]

theorem bitN_eq' (x i : ℕ) : bitN x i = (x.testBit i).toNat := by
  rw [Nat.toNat_testBit]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem mod_two_pow_succ (c n : ℕ) :
    c % 2 ^ (n + 1) = c % 2 ^ n + 2 ^ n * (c.testBit n).toNat := by
  rw [Nat.toNat_testBit, Nat.mod_pow_succ]

theorem mulC_loop {c x p : ℕ} (hx : x < 2 ^ (4 * SX)) (hp : p < SX) : ∀ n, n ≤ 4 →
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun b acc => Bool.rec (motive := fun _ => ℕ) acc
        (add15 SX acc (rotk SX b x)) (Nat.beq (bitN c b) (nat_lit 1))) n < 2 ^ (4 * SX) ∧
      resP SX (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun b acc => Bool.rec (motive := fun _ => ℕ)
        acc (add15 SX acc (rotk SX b x)) (Nat.beq (bitN c b) (nat_lit 1))) n) p =
        ((c % 2 ^ n : ℕ) : ZMod 15) * resP SX x p
  | 0, _ => ⟨Nat.two_pow_pos _, by
      change resP SX 0 p = _
      rw [resP_zero']
      simp [Nat.mod_one]⟩
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := mulC_loop hx hp n (by omega)
    change Bool.rec (motive := fun _ => ℕ) _ (add15 SX _ (rotk SX n x))
      (Nat.beq (bitN c n) (nat_lit 1)) < _ ∧ resP SX (Bool.rec (motive := fun _ => ℕ) _
        (add15 SX _ (rotk SX n x)) (Nat.beq (bitN c n) (nat_lit 1))) p = _
    rw [bitN_eq', mod_two_pow_succ]
    cases hb : c.testBit n
    · change Nat.rec (motive := fun _ => ℕ) _ _ n < _ ∧
        resP SX (Nat.rec (motive := fun _ => ℕ) _ _ n) p = _
      exact ⟨ih1, by rw [ih2]; simp⟩
    · refine ⟨add15_lt ih1 (rotk_lt _ _ _), ?_⟩
      change resP SX (add15 SX _ (rotk SX n x)) p = _
      rw [resP_add15 ih1 (rotk_lt _ _ _) hp, ih2, resP_rotk (by omega) hx hp, Bool.toNat_true]
      push_cast
      ring

theorem mulC_lt (c x : ℕ) (hx : x < 2 ^ (4 * SX)) : mulC c x < 2 ^ (4 * SX) :=
  (mulC_loop (p := 0) hx (by decide) 4 le_rfl).1

theorem resP_mulC {c x p : ℕ} (hc : c < 16) (hx : x < 2 ^ (4 * SX)) (hp : p < SX) :
    resP SX (mulC c x) p = (c : ZMod 15) * resP SX x p := by
  have := (mulC_loop (c := c) hx hp 4 le_rfl).2
  rw [Nat.mod_eq_of_lt (by simpa using hc)] at this
  exact this

theorem testBit_plane {S b x p : ℕ} (hp : p < S) : (plane S b x).testBit p = x.testBit (b * S + p) := by
  unfold plane
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, Benes.ones_eq,
    Nat.testBit_two_pow_sub_one, decide_eq_true hp, Bool.and_true]

theorem plane_lt (S b x : ℕ) : plane S b x < 2 ^ S := by
  unfold plane
  rw [nland, Benes.ones_eq]
  exact Benes.land_ones_lt _ _

theorem testBit_rep4' {S m : ℕ} (hm : m < 2 ^ S) {i p : ℕ} (hi : i < 4) (hp : p < S) :
    (rep4 S m).testBit (i * S + p) = m.testBit p := by
  have hz : ∀ t, S ≤ t → m.testBit t = false := fun t ht =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) ht))
  unfold rep4
  simp only [nlor, nshl, Nat.testBit_or, Nat.testBit_shiftLeft]
  have e : S <<< 1 = 2 * S := by rw [Nat.shiftLeft_eq, pow_one, Nat.mul_comm]
  rw [e]
  interval_cases i <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, hz, Bool.and_true, Bool.true_and,
      Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and, Nat.zero_mul, Nat.zero_add,
      Nat.one_mul] <;>
    congr 1 <;> omega

theorem dg_rep4 {S m p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    dg S (rep4 S m) p = if m.testBit p then 15 else 0 := by
  refine dg_ext (dg_lt _ _ _) (by split <;> decide) fun i hi => ?_
  rw [testBit_dg, decide_eq_true hi, Bool.true_and, testBit_rep4' hm hi hp]
  cases m.testBit p <;> interval_cases i <;> rfl

theorem rotk_one_lt : ∀ a < 16, ∀ b < 4, rotk 1 b a < 16 := by decide +kernel

theorem resP_mulV_term {b x y p : ℕ} (hb : b < 4) (hx : x < 2 ^ (4 * SX)) (hp : p < SX) :
    resP SX (Nat.land (rotk SX b x) (rep4 SX (plane SX b y))) p =
      (((y.testBit (b * SX + p)).toNat * 2 ^ b : ℕ) : ZMod 15) * resP SX x p := by
  rw [resP_dg, dg_and, dg_rotk (by omega) hx hp, dg_rep4 (plane_lt _ _ _) hp, testBit_plane hp]
  cases y.testBit (b * SX + p)
  · simp
  · rw [Bool.toNat_true]
    have h15 : Nat.land (rotk 1 b (dg SX x p)) 15 = rotk 1 b (dg SX x p) := by
      rw [nland, (by rfl : (15 : ℕ) = 2 ^ 4 - 1), Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (rotk_one_lt _ (dg_lt SX x p) _ hb)]
    rw [ite_eq_left rfl, h15, ← ZMod.natCast_mod, rotk_one_mod _ (dg_lt SX x p) _ hb, ZMod.natCast_mod,
      resP_dg]
    push_cast
    ring

theorem mulV_loop {x y p : ℕ} (hx : x < 2 ^ (4 * SX)) (hp : p < SX) : ∀ n, n ≤ 4 →
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun b acc =>
        add15 SX acc (Nat.land (rotk SX b x) (rep4 SX (plane SX b y)))) n < 2 ^ (4 * SX) ∧
      resP SX (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun b acc =>
        add15 SX acc (Nat.land (rotk SX b x) (rep4 SX (plane SX b y)))) n) p =
        ((∑ b ∈ Finset.range n, (y.testBit (b * SX + p)).toNat * 2 ^ b : ℕ) : ZMod 15) *
          resP SX x p
  | 0, _ => ⟨Nat.two_pow_pos _, by
      change resP SX 0 p = _
      rw [resP_zero']
      simp⟩
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := mulV_loop hx hp n (by omega)
    have ht : Nat.land (rotk SX n x) (rep4 SX (plane SX n y)) < 2 ^ (4 * SX) :=
      lt4_and (rotk_lt _ _ _)
    refine ⟨add15_lt ih1 ht, ?_⟩
    change resP SX (add15 SX _ _) p = _
    rw [resP_add15 ih1 ht hp, ih2, resP_mulV_term (by omega) hx hp, Finset.sum_range_succ]
    push_cast
    ring

theorem mulV_lt (x y : ℕ) (hx : x < 2 ^ (4 * SX)) : mulV x y < 2 ^ (4 * SX) :=
  (mulV_loop (y := y) (p := 0) hx (by decide) 4 le_rfl).1

theorem dg_sum (S y p : ℕ) :
    ∑ b ∈ Finset.range 4, (y.testBit (b * S + p)).toNat * 2 ^ b = dg S y p := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, dg]
  ring_nf

theorem resP_mulV {x y p : ℕ} (hx : x < 2 ^ (4 * SX)) (hp : p < SX) :
    resP SX (mulV x y) p = resP SX y p * resP SX x p := by
  have := (mulV_loop (y := y) hx hp 4 le_rfl).2
  rw [dg_sum] at this
  rw [resP_dg SX y]
  exact this

theorem fold15 {g : ℕ → ℕ} (hg : ∀ m, g m < 2 ^ (4 * SX)) {p : ℕ} (hp : p < SX) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
        (fun m acc => strictN (add15 SX acc (g m)) (fun y => y)) n < 2 ^ (4 * SX) ∧
      resP SX (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
        (fun m acc => strictN (add15 SX acc (g m)) (fun y => y)) n) p =
        ∑ m ∈ Finset.range n, resP SX (g m) p
  | 0 => ⟨Nat.two_pow_pos _, by
      change resP SX 0 p = _
      rw [resP_zero']
      simp⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := fold15 hg hp n
    change strictN (add15 SX _ (g n)) (fun y => y) < _ ∧
      resP SX (strictN (add15 SX _ (g n)) (fun y => y)) p = _
    rw [Benes.strictN_eq]
    exact ⟨add15_lt ih1 (hg n), by rw [resP_add15 ih1 (hg n) hp, ih2, Finset.sum_range_succ]⟩

theorem land_m4_lt (S y : ℕ) : Nat.land y (m4 S) < 2 ^ (4 * S) := by
  rw [m4_eq, nland]
  exact Benes.land_ones_lt _ _

theorem uVec_lt (U l : ℕ) : uVec U l < 2 ^ (4 * SX) := land_m4_lt SX _

theorem mEnt_lt (MK k i j : ℕ) : mEnt MK k i j < 16 := by
  unfold mEnt
  rw [nland]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

@[expose] noncomputable def qInner (U MK k l : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun m acc2 => strictN (add15 SX acc2 (mulC (mEnt MK k l m) (uVec U m))) (fun y => y))
    (nat_lit 24)

theorem qVec_eq (U MK k : ℕ) : qVec U MK k = Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun l acc => strictN (add15 SX acc (mulV (uVec U l) (qInner U MK k l))) (fun y => y))
    (nat_lit 24) := rfl

theorem resP_qVec (U MK k : ℕ) {p : ℕ} (hp : p < SX) :
    qVec U MK k < 2 ^ (4 * SX) ∧ resP SX (qVec U MK k) p =
      ∑ l ∈ Finset.range 24, resP SX (uVec U l) p *
        ∑ m ∈ Finset.range 24, (mEnt MK k l m : ZMod 15) * resP SX (uVec U m) p := by
  have hin : ∀ l, qInner U MK k l < 2 ^ (4 * SX) ∧ resP SX (qInner U MK k l) p =
      ∑ m ∈ Finset.range 24, resP SX (mulC (mEnt MK k l m) (uVec U m)) p :=
    fun l => fold15 (g := fun m => mulC (mEnt MK k l m) (uVec U m))
      (fun m => mulC_lt _ _ (uVec_lt U m)) hp (nat_lit 24)
  have h := fold15 (g := fun l => mulV (uVec U l) (qInner U MK k l))
    (fun l => mulV_lt _ _ (uVec_lt U l)) hp (nat_lit 24)
  rw [qVec_eq]
  refine ⟨h.1, ?_⟩
  refine h.2.trans (Finset.sum_congr rfl fun l _ => ?_)
  rw [resP_mulV (uVec_lt U l) hp, (hin l).2]
  exact (mul_comm _ _).trans (congrArg _ (Finset.sum_congr rfl fun m _ =>
    resP_mulC (mEnt_lt _ _ _ _) (uVec_lt U m) hp))

@[expose] def dig3 (S d p : ℕ) : ℕ :=
  (d.testBit (0 * S + p)).toNat + 2 * (d.testBit (1 * S + p)).toNat +
    4 * (d.testBit (2 * S + p)).toNat

theorem testBit_ones' (W q : ℕ) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem dig3_lt (S d p : ℕ) : dig3 S d p < 8 := by
  unfold dig3
  cases d.testBit (0 * S + p) <;> cases d.testBit (1 * S + p) <;> cases d.testBit (2 * S + p) <;>
    decide

theorem testBit_selR {P r b p : ℕ} (hp : p < SX) :
    (Bool.rec (motive := fun _ => ℕ) (Nat.xor (ones SX) P) P (Nat.beq (bitN r b) 1)).testBit p =
      (P.testBit p == r.testBit b) := by
  rw [bitN_eq']
  cases r.testBit b
  · change (Nat.xor (ones SX) P).testBit p = _
    rw [nxor, Nat.testBit_xor, testBit_ones', decide_eq_true hp]
    cases P.testBit p <;> rfl
  · change P.testBit p = _
    cases P.testBit p <;> rfl

theorem testBit_mr {x r p : ℕ} (hr : r < 16) (hp : p < SX) :
    (Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 0 x))
        (plane SX 0 x) (Nat.beq (bitN r 0) 1))
        (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 1 x)) (plane SX 1 x)
          (Nat.beq (bitN r 1) 1)))
      (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 2 x))
        (plane SX 2 x) (Nat.beq (bitN r 2) 1))
        (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 3 x)) (plane SX 3 x)
          (Nat.beq (bitN r 3) 1)))).testBit p = decide (dg SX x p = r) := by
  simp only [nland, Nat.testBit_and, testBit_selR hp, testBit_plane hp]
  have hd := dg_lt SX x p
  have key : dg SX x p = r ↔ ∀ i < 4, (dg SX x p).testBit i = r.testBit i :=
    ⟨fun h i _ => by rw [h], fun h => dg_ext hd hr h⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, key]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩ i hi
    rw [testBit_dg, decide_eq_true hi, Bool.true_and]
    interval_cases i <;> assumption
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    rw [testBit_dg, decide_eq_true (by decide), Bool.true_and] at h0 h1 h2 h3
    exact ⟨⟨h0, h1⟩, h2, h3⟩

theorem testBit_selB_shl {c m t b : ℕ} (hc : c < 2) (hm : m < 2 ^ SX) :
    (Nat.shiftLeft (selB c m) (Nat.mul b SX)).testBit t = true ↔
      b * SX ≤ t ∧ t - b * SX < SX ∧ c = 1 ∧ m.testBit (t - b * SX) = true := by
  rw [InitAux.testBit_shl]
  unfold selB
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · simp
  · simp only [nmul, Nat.one_mul, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_, h2⟩
      by_contra hc
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide)
        (by omega)))] at h2
      exact Bool.false_ne_true h2
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩

theorem mr_lt (x r : ℕ) :
    Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 0 x))
        (plane SX 0 x) (Nat.beq (bitN r 0) 1))
        (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 1 x)) (plane SX 1 x)
          (Nat.beq (bitN r 1) 1)))
      (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 2 x))
        (plane SX 2 x) (Nat.beq (bitN r 2) 1))
        (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX 3 x)) (plane SX 3 x)
          (Nat.beq (bitN r 3) 1))) < 2 ^ SX := by
  have hb : ∀ b, Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) (plane SX b x))
      (plane SX b x) (Nat.beq (bitN r b) 1) < 2 ^ SX := by
    intro b
    cases Nat.beq (bitN r b) 1
    · exact Nat.xor_lt_two_pow (by rw [Benes.ones_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) (by decide))
        (plane_lt _ _ _)
    · exact plane_lt _ _ _
  exact lt_of_le_of_lt Nat.and_le_left (lt_of_le_of_lt Nat.and_le_left (hb 0))

theorem testBit_dig5 {x b p : ℕ} (hb : b < 3) (hp : p < SX) :
    (dig5 x).testBit (b * SX + p) = (dg SX x p % 15 % 5).testBit b := by
  have hS : SX = 131072 := rfl
  have hv : ∀ r b', bitN (Nat.mod (Nat.mod r 15) 5) b' < 2 := fun r b' => by
    rw [bitN_eq']
    exact Bool.toNat_lt _
  have hd := dg_lt SX x p
  unfold dig5
  dsimp only
  rw [Bool.eq_iff_iff, InitAux.testBit_foldOr]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨r, hr, h⟩
    rw [InitAux.testBit_foldOr] at h
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at h
    obtain ⟨b', hb', h⟩ := h
    rw [testBit_selB_shl (hv r b') (mr_lt x r)] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have e : b' = b := by
      rw [hS] at h1 h2 hp
      omega
    subst e
    rw [Nat.add_sub_cancel_left, testBit_mr hr hp, decide_eq_true_iff] at h4
    subst h4
    rw [bitN_eq'] at h3
    simp only [nmod] at h3
    cases hc : (dg SX x p % 15 % 5).testBit b'
    · rw [hc] at h3
      exact absurd h3 (by decide)
    · rfl
  · intro h
    refine ⟨dg SX x p, hd, ?_⟩
    rw [InitAux.testBit_foldOr]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    refine ⟨b, hb, ?_⟩
    rw [testBit_selB_shl (hv _ b) (mr_lt x _), Nat.add_sub_cancel_left, testBit_mr hd hp,
      bitN_eq']
    simp only [nmod]
    rw [h]
    exact ⟨Nat.le_add_right _ _, hp, rfl, decide_eq_true trivial⟩

theorem small_digits : ∀ v < 8,
    (v.testBit 0).toNat + 2 * (v.testBit 1).toNat + 4 * (v.testBit 2).toNat = v := by
  decide

theorem dig3_dig5 {x p : ℕ} (hp : p < SX) : dig3 SX (dig5 x) p = dg SX x p % 15 % 5 := by
  unfold dig3
  rw [testBit_dig5 (by decide) hp, testBit_dig5 (by decide) hp, testBit_dig5 (by decide) hp]
  exact small_digits _ (by omega)

theorem lex_bool : ∀ d0 d1 d2 e0 e1 e2 : Bool,
    (((true ^^ d2) && e2) || ((true ^^ (d2 ^^ e2)) && (((true ^^ d1) && e1) ||
      ((true ^^ (d1 ^^ e1)) && ((true ^^ d0) && e0))))) =
      decide (d0.toNat + 2 * d1.toNat + 4 * d2.toNat < e0.toNat + 2 * e1.toNat + 4 * e2.toNat) ∧
    ((true ^^ (d2 ^^ e2)) && ((true ^^ (d1 ^^ e1)) && (true ^^ (d0 ^^ e0)))) =
      decide (d0.toNat + 2 * d1.toNat + 4 * d2.toNat = e0.toNat + 2 * e1.toNat + 4 * e2.toNat) := by
  decide

theorem lexStep_bits {lt eq d e r : ℕ} (hr : r < SX)
    (he : ∀ b < 3, (plane SX b e).testBit r = d.testBit (b * SX + (r + 1))) :
    (lexStep lt eq d e).1.testBit r =
        (lt.testBit r || (eq.testBit r && decide (dig3 SX d r < dig3 SX d (r + 1)))) ∧
      (lexStep lt eq d e).2.testBit r =
        (eq.testBit r && decide (dig3 SX d r = dig3 SX d (r + 1))) := by
  unfold lexStep
  dsimp only
  simp only [nlor, nland, nxor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    testBit_ones', decide_eq_true hr, he 0 (by decide), he 1 (by decide), he 2 (by decide),
    testBit_plane hr]
  unfold dig3
  obtain ⟨l1, l2⟩ := lex_bool (d.testBit (0 * SX + r)) (d.testBit (1 * SX + r))
    (d.testBit (2 * SX + r)) (d.testBit (0 * SX + (r + 1))) (d.testBit (1 * SX + (r + 1)))
    (d.testBit (2 * SX + (r + 1)))
  rw [l1, l2]
  exact ⟨rfl, rfl⟩

end CFSG.KC.KDense.P15

end
