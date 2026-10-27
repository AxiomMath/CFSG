module

public import Mathlib.Data.ZMod.Basic
public import CFSG.Certificates.Kernel.Pc3.Coll
public import Certificates.Data.Kernel.Fi23Q.Census
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group

public section

namespace CFSG.KS.Fi23Q

open CFSG.KC.Enum CFSG.KC.Pc3 CFSG.KC.Fi23Q CFSG.KS.Pc3

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem band_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem pow4 (k : ℕ) : (2 : ℕ) ^ (k <<< 1) = 4 ^ k := by
  rw [Nat.shiftLeft_eq, pow_one, mul_comm, pow_mul]
  norm_num

theorem dg_eq (u k : ℕ) : dg u k = u / 4 ^ k % 4 := by
  change u >>> (k <<< 1) &&& 3 = _
  rw [Nat.shiftRight_eq_div_pow, pow4, show (3 : ℕ) = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem dg_lt (u k : ℕ) : dg u k < 4 := by
  rw [dg_eq]
  omega

theorem dg_four_mul_add (a b : ℕ) (hb : b < 4) (k : ℕ) :
    dg (4 * a + b) (k + 1) = dg a k := by
  rw [dg_eq, dg_eq, pow_succ, mul_comm (4 ^ k), ← Nat.div_div_eq_div_mul]
  congr 2
  omega

theorem dg_four_mul_add_zero (a b : ℕ) (hb : b < 4) : dg (4 * a + b) 0 = b := by
  rw [dg_eq]
  simp
  omega

theorem vecOK_dg {u : ℕ} (h : vecOK 13 u = true) (k : ℕ) : dg u k < 3 := by
  obtain ⟨h1, h2⟩ := band_true h
  have hlt : u < 4 ^ 13 := by
    simp only [Nat.blt_eq] at h1
    simpa [Nat.shiftLeft_eq] using h1
  have h0 : u &&& (u >>> 1) &&& 1431655765 = 0 := Nat.eq_of_beq_eq_true h2
  by_cases hk : 13 ≤ k
  · rw [dg_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk))]
    norm_num
  · have h3 := dg_lt u k
    by_contra hc
    have e : dg u k = 3 := by omega
    have eb : u >>> (k <<< 1) &&& 3 = 3 := e
    have b0 : (u >>> (k <<< 1) &&& 3).testBit 0 = true := by rw [eb]; decide
    have b1 : (u >>> (k <<< 1) &&& 3).testBit 1 = true := by rw [eb]; decide
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true, Nat.add_zero] at b0 b1
    have hm : (1431655765 : ℕ).testBit (k <<< 1) = true := by
      rw [Nat.shiftLeft_eq]
      interval_cases k <;> decide
    have := congrArg (fun z => z.testBit (k <<< 1)) h0
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rw [hm, show 1 + k <<< 1 = k <<< 1 + 1 by omega, b0.1, b1.1] at this
    simp at this

@[expose] def nib (v k : ℕ) : ℕ := v / 16 ^ k % 16

@[expose] def Gd (m v : ℕ) : Prop := v < 16 ^ m ∧ ∀ k < m, nib v k < 3

theorem nib_zero (a b : ℕ) (hb : b < 16) : nib (16 * a + b) 0 = b := by
  simp [nib]
  omega

theorem nib_succ (a b : ℕ) (hb : b < 16) (k : ℕ) : nib (16 * a + b) (k + 1) = nib a k := by
  rw [nib, nib, pow_succ, mul_comm (16 ^ k), ← Nat.div_div_eq_div_mul]
  congr 2
  omega

theorem Gd_succ {m a b : ℕ} (hb : b < 3) (ha : Gd m a) : Gd (m + 1) (16 * a + b) := by
  refine ⟨by rw [pow_succ]; have := ha.1; omega, fun k hk => ?_⟩
  rcases k with _ | k
  · rw [nib_zero a b (by omega)]
    exact hb
  · rw [nib_succ a b (by omega)]
    exact ha.2 k (by omega)

theorem Gd_split {m v : ℕ} (h : Gd (m + 1) v) :
    v = 16 * (v / 16) + v % 16 ∧ v % 16 < 3 ∧ Gd m (v / 16) := by
  refine ⟨(Nat.div_add_mod v 16).symm, ?_, ?_, fun k hk => ?_⟩
  · have := h.2 0 (by omega)
    simpa [nib] using this
  · have := h.1
    rw [pow_succ] at this
    omega
  · have := h.2 (k + 1) (by omega)
    rwa [(Nat.div_add_mod v 16).symm, nib_succ _ _ (Nat.mod_lt _ (by norm_num))] at this

@[expose] def maskF (C s : ℕ) : ℕ := ((s >>> 2) ||| (s &&& (s >>> 1))) &&& C

theorem testBit_16 {t s0 : ℕ} (h : s0 < 16) (j : ℕ) :
    (16 * t + s0).testBit j = if j < 4 then s0.testBit j else t.testBit (j - 4) :=
  Nat.testBit_two_pow_mul_add t (b := s0) (i := 4) h j

theorem maskF_step {C s0 t : ℕ} (h : s0 ≤ 4) :
    maskF (16 * C + 1) (16 * t + s0) = 16 * maskF C t + (if 3 ≤ s0 then 1 else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hr : (if 3 ≤ s0 then 1 else 0) < 16 := by split <;> omega
  rw [testBit_16 hr]
  simp only [maskF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    testBit_16 (show s0 < 16 by omega), testBit_16 (show 1 < 16 by omega)]
  by_cases hi : i < 4
  · interval_cases i <;> interval_cases s0 <;> simp [Nat.testBit_eq_decide_div_mod_eq]
  · have n2 : ¬ 2 + i < 4 := by omega
    have n1 : ¬ 1 + i < 4 := by omega
    have e2 : 2 + i - 4 = 2 + (i - 4) := by omega
    have e1 : 1 + i - 4 = 1 + (i - 4) := by omega
    simp only [if_neg hi, if_neg n2, if_neg n1, e1, e2]

@[expose] def mC : ℕ → ℕ
  | 0 => 0
  | m + 1 => 16 * mC m + 1

theorem maskF_zero (s : ℕ) : maskF 0 s = 0 := by simp [maskF]

theorem nAdd_aux : ∀ m x y, Gd m x → Gd m y →
    3 * maskF (mC m) (x + y) ≤ x + y ∧ Gd m (x + y - 3 * maskF (mC m) (x + y)) ∧
      ∀ k < m, nib (x + y - 3 * maskF (mC m) (x + y)) k = (nib x k + nib y k) % 3
  | 0, x, y, hx, hy => by
    have : x = 0 := by have := hx.1; simp at this; omega
    have : y = 0 := by have := hy.1; simp at this; omega
    subst x y
    simp [mC, maskF_zero, Gd]
  | m + 1, x, y, hx, hy => by
    obtain ⟨ex, x0, hx'⟩ := Gd_split hx
    obtain ⟨ey, y0, hy'⟩ := Gd_split hy
    obtain ⟨i1, i2, i3⟩ := nAdd_aux m _ _ hx' hy'
    have es : x + y = 16 * (x / 16 + y / 16) + (x % 16 + y % 16) := by omega
    have hm : maskF (mC (m + 1)) (x + y) =
        16 * maskF (mC m) (x / 16 + y / 16) + (if 3 ≤ x % 16 + y % 16 then 1 else 0) := by
      rw [es, mC, maskF_step (by omega)]
    set M := maskF (mC m) (x / 16 + y / 16)
    set r := x / 16 + y / 16 - 3 * M
    have er : x + y - 3 * maskF (mC (m + 1)) (x + y) =
        16 * r + (x % 16 + y % 16 - 3 * (if 3 ≤ x % 16 + y % 16 then 1 else 0)) := by
      rw [hm]
      split <;> omega
    have hlow : x % 16 + y % 16 - 3 * (if 3 ≤ x % 16 + y % 16 then 1 else 0) =
        (x % 16 + y % 16) % 3 := by
      split <;> omega
    refine ⟨by rw [hm]; split <;> omega, ?_, fun k hk => ?_⟩
    · rw [er, hlow]
      exact Gd_succ (Nat.mod_lt _ (by norm_num)) i2
    · rw [er, hlow]
      rcases k with _ | k
      · rw [nib_zero _ _ (by omega)]
        conv_rhs => rw [ex, ey, nib_zero _ _ (by omega), nib_zero _ _ (by omega)]
      · rw [nib_succ _ _ (by omega), i3 k (by omega)]
        conv_rhs => rw [ex, ey, nib_succ _ _ (by omega), nib_succ _ _ (by omega)]

theorem mC_five : mC 5 = 69905 := rfl

theorem nAdd_eq (x y : ℕ) : nAdd x y = x + y - 3 * maskF (mC 5) (x + y) := by
  unfold nAdd
  rw [strictN_eq]
  rfl

theorem nAdd_spec {x y : ℕ} (hx : Gd 5 x) (hy : Gd 5 y) :
    Gd 5 (nAdd x y) ∧ ∀ k < 5, (nib (nAdd x y) k : ZMod 3) = nib x k + nib y k := by
  obtain ⟨-, h2, h3⟩ := nAdd_aux 5 x y hx hy
  rw [nAdd_eq]
  refine ⟨h2, fun k hk => ?_⟩
  rw [h3 k hk]
  push_cast [ZMod.natCast_mod]
  rfl

theorem d3_eq (b k : ℕ) : d3 b k = b / 3 ^ k % 3 := rfl

theorem d3_lt (b k : ℕ) : d3 b k < 3 := Nat.mod_lt _ (by norm_num)

theorem d3_div (a k : ℕ) : d3 (a / 3) k = d3 a (k + 1) := by
  rw [d3_eq, d3_eq, Nat.div_div_eq_div_mul, pow_succ', mul_comm]

theorem b3v_succ (m s x : ℕ) : b3v (m + 1) s x = x % 3 + b3v m s (x / 3) <<< s := rfl

theorem b3v_zero (s x : ℕ) : b3v 0 s x = 0 := rfl

theorem b3v4 : ∀ m a, Gd m (b3v m 4 a) ∧ ∀ k < m, nib (b3v m 4 a) k = d3 a k
  | 0, a =>
    ⟨⟨by simp [b3v_zero], fun k hk => absurd hk (by omega)⟩, fun k hk => absurd hk (by omega)⟩
  | m + 1, a => by
    have e : b3v (m + 1) 4 a = 16 * b3v m 4 (a / 3) + a % 3 := by
      rw [b3v_succ, Nat.shiftLeft_eq]
      ring
    obtain ⟨g, h⟩ := b3v4 m (a / 3)
    rw [e]
    refine ⟨Gd_succ (Nat.mod_lt _ (by norm_num)) g, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [nib_zero _ _ (by omega), d3_eq]
      simp
    · rw [nib_succ _ _ (by omega), h k (by omega), d3_div]

theorem b3v2 : ∀ m a k, dg (b3v m 2 a) k = if k < m then d3 a k else 0
  | 0, a, k => by simp [b3v_zero, dg_eq]
  | m + 1, a, k => by
    have e : b3v (m + 1) 2 a = 4 * b3v m 2 (a / 3) + a % 3 := by
      rw [b3v_succ, Nat.shiftLeft_eq]
      ring
    rw [e]
    rcases k with _ | k
    · rw [dg_four_mul_add_zero _ _ (by omega), d3_eq]
      simp
    · rw [dg_four_mul_add _ _ (by omega), b3v2 m (a / 3) k, d3_div]
      by_cases hk : k < m
      · simp [hk]
      · simp [hk, show ¬ k + 1 < m + 1 by omega]

@[expose] noncomputable def nibR (m x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih x => (x &&& 3) + (ih (x >>> 2)) <<< 4) m x

theorem nibA_eq (u : ℕ) : nibA u = nibR 5 (u >>> 16) := rfl

theorem nibR_spec : ∀ m x, (∀ k < m, x / 4 ^ k % 4 < 3) →
    Gd m (nibR m x) ∧ ∀ k < m, nib (nibR m x) k = x / 4 ^ k % 4
  | 0, x, _ =>
    ⟨⟨by simp [nibR], fun k hk => absurd hk (by omega)⟩, fun k hk => absurd hk (by omega)⟩
  | m + 1, x, hx => by
    have e : nibR (m + 1) x = 16 * nibR m (x / 4) + x % 4 := by
      change (x &&& 3) + (nibR m (x >>> 2)) <<< 4 = _
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show (3 : ℕ) = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      norm_num
      ring
    have hx' : ∀ k < m, x / 4 / 4 ^ k % 4 < 3 := fun k hk => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact hx (k + 1) (by omega)
    obtain ⟨g, h⟩ := nibR_spec m (x / 4) hx'
    have h0 := hx 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    rw [e]
    refine ⟨Gd_succ h0 g, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [nib_zero _ _ (by omega)]
      simp
    · rw [nib_succ _ _ (by omega), h k (by omega), Nat.div_div_eq_div_mul, ← pow_succ']

theorem vecOK_lt {u : ℕ} (h : vecOK 13 u = true) : u < 4 ^ 13 := by
  obtain ⟨h1, -⟩ := band_true h
  simp only [Nat.blt_eq] at h1
  simpa [Nat.shiftLeft_eq] using h1

theorem nibA_spec {u : ℕ} (h : vecOK 13 u = true) :
    Gd 5 (nibA u) ∧ ∀ k < 5, nib (nibA u) k = dg u (8 + k) := by
  have e : ∀ k, u >>> 16 / 4 ^ k % 4 = dg u (8 + k) := fun k => by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, dg_eq, pow_add]
    norm_num
  rw [nibA_eq]
  obtain ⟨g, hh⟩ := nibR_spec 5 (u >>> 16) (fun k _ => by rw [e]; exact vecOK_dg h _)
  exact ⟨g, fun k hk => by rw [hh k hk, e]⟩

theorem nSc_eq (e x : ℕ) : nSc e x = if e = 0 then 0 else if e = 1 then x else nAdd x x := by
  unfold nSc
  by_cases h0 : e = 0
  · subst h0
    rfl
  · by_cases h1 : e = 1
    · subst h1
      rfl
    · have a : Nat.beq e 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      have b : Nat.beq e 1 = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
      rw [if_neg h0, if_neg h1, a, b]

theorem Gd_zero (m : ℕ) : Gd m 0 := ⟨by positivity, fun k _ => by simp [nib]⟩

theorem nSc_spec {e x : ℕ} (he : e < 3) (hx : Gd 5 x) :
    Gd 5 (nSc e x) ∧ ∀ k < 5, (nib (nSc e x) k : ZMod 3) = e * nib x k := by
  rw [nSc_eq]
  by_cases h0 : e = 0
  · subst h0
    simp [Gd_zero, nib]
  · by_cases h1 : e = 1
    · subst h1
      simp [hx]
    · have h2 : e = 2 := by omega
      subst h2
      obtain ⟨g, hh⟩ := nAdd_spec hx hx
      simp only [if_neg h0, if_neg h1]
      exact ⟨g, fun k hk => by rw [hh k hk]; push_cast; ring⟩

@[expose] noncomputable def mulMR (MV b m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => strictN acc fun s => nAdd s (nSc (d3 b k) (nibA (f32 MV k)))) m

theorem mulM_eq (MV b : ℕ) : mulM MV b = mulMR MV b 5 := rfl

theorem mulMR_succ (MV b m : ℕ) :
    mulMR MV b (m + 1) = nAdd (mulMR MV b m) (nSc (d3 b m) (nibA (f32 MV m))) := by
  change strictN (mulMR MV b m) (fun s => nAdd s (nSc (d3 b m) (nibA (f32 MV m)))) = _
  rw [strictN_eq]

theorem mulMR_spec {MV b : ℕ} (hM : ∀ l < 5, vecOK 13 (f32 MV l) = true) : ∀ m, m ≤ 5 →
    Gd 5 (mulMR MV b m) ∧ ∀ k < 5, (nib (mulMR MV b m) k : ZMod 3) =
      ((List.range m).map fun l => (d3 b l : ZMod 3) * (dg (f32 MV l) (8 + k) : ZMod 3)).sum
  | 0, _ => ⟨Gd_zero 5, fun k _ => by simp [mulMR, nib]⟩
  | m + 1, hm => by
    obtain ⟨g, hh⟩ := mulMR_spec hM m (by omega)
    obtain ⟨gA, hA⟩ := nibA_spec (hM m (by omega))
    obtain ⟨gS, hS⟩ := nSc_spec (d3_lt b m) gA
    obtain ⟨gN, hN⟩ := nAdd_spec g gS
    rw [mulMR_succ]
    refine ⟨gN, fun k hk => ?_⟩
    rw [hN k hk, hh k hk, hS k hk, hA k hk, List.range_succ, List.map_append, List.sum_append]
    simp

variable {G : Type*} [Group G]

@[expose] def wd (x : ℕ → G) (u : List ℕ) : G := (u.map x).prod

theorem wd_append (x : ℕ → G) (u v : List ℕ) : wd x (u ++ v) = wd x u * wd x v := by
  simp [wd]

theorem wd_cons (x : ℕ → G) (a : ℕ) (u : List ℕ) : wd x (a :: u) = x a * wd x u := by
  simp [wd]

theorem wd_nil (x : ℕ → G) : wd x [] = 1 := by simp [wd]

@[expose] noncomputable def nwF (n u m : ℕ) (acc : List ℕ) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ)
    (Bool.rec (motive := fun _ => List ℕ) ((n - 1 - m) :: (n - 1 - m) :: acc) ((n - 1 - m) :: acc)
      (Nat.beq (dg u (n - 1 - m)) 1))
    acc (Nat.beq (dg u (n - 1 - m)) 0)

theorem nwR_eq (n u : ℕ) :
    nwR n u = Nat.rec (motive := fun _ => List ℕ) [] (fun m acc => nwF n u m acc) n := rfl

theorem nwF_spec (x : ℕ → G) (n u m : ℕ) (acc : List ℕ) (hd : dg u (n - 1 - m) < 3) :
    wd x (nwF n u m acc) = x (n - 1 - m) ^ dg u (n - 1 - m) * wd x acc ∧
      ∀ c ∈ nwF n u m acc, c = n - 1 - m ∨ c ∈ acc := by
  have b00 : Nat.beq 0 0 = true := rfl
  have b10 : Nat.beq 1 0 = false := rfl
  have b11 : Nat.beq 1 1 = true := rfl
  have b20 : Nat.beq 2 0 = false := rfl
  have b21 : Nat.beq 2 1 = false := rfl
  unfold nwF
  obtain h | h | h : dg u (n - 1 - m) = 0 ∨ dg u (n - 1 - m) = 1 ∨ dg u (n - 1 - m) = 2 := by
    omega
  all_goals
    simp only [h, b00, b10, b11, b20, b21]
    refine ⟨by simp [wd_cons, pow_two, mul_assoc], fun c hc => ?_⟩
    try simp only [List.mem_cons] at hc
    tauto

theorem nwR_aux (x : ℕ → G) (n u : ℕ) (hd : ∀ k, dg u k < 3) : ∀ m, m ≤ n →
    wd x (Nat.rec (motive := fun _ => List ℕ) [] (fun m acc => nwF n u m acc) m) =
      ((List.range m).map fun i => x (n - m + i) ^ dg u (n - m + i)).prod ∧
    ∀ c ∈ Nat.rec (motive := fun _ => List ℕ) [] (fun m acc => nwF n u m acc) m, c < n
  | 0, _ => ⟨by simp [wd], fun c hc => absurd hc (by simp)⟩
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := nwR_aux x n u hd m (by omega)
    obtain ⟨f1, f2⟩ := nwF_spec x n u m
      (Nat.rec (motive := fun _ => List ℕ) [] (fun m acc => nwF n u m acc) m) (hd _)
    refine ⟨?_, fun c hc => ?_⟩
    · change wd x (nwF n u m _) = _
      rw [f1, ih1, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      have e0 : n - (m + 1) + 0 = n - 1 - m := by omega
      have e1 : ∀ i, n - (m + 1) + (i + 1) = n - m + i := fun i => by omega
      rw [e0]
      congr 2
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, e1]
    · rcases f2 c hc with h | h
      · omega
      · exact ih2 c h

theorem nwR_spec (x : ℕ → G) {u : ℕ} (hd : ∀ k, dg u k < 3) :
    wd x (nwR 13 u) = nv x 13 u ∧ ∀ c ∈ nwR 13 u, c < 13 := by
  obtain ⟨h1, h2⟩ := nwR_aux x 13 u hd 13 le_rfl
  rw [nwR_eq]
  refine ⟨?_, h2⟩
  rw [h1]
  simp [nv]

@[expose] def pR (g : ℕ → G) (m : ℕ) (v : ℕ → ZMod 3) : G :=
  ((List.range m).map fun l => g l ^ (v l).val).prod

@[expose] def aEl (x : ℕ → G) (v : ℕ → ZMod 3) : G := pR (fun l => x (8 + l)) 5 v

@[expose] noncomputable def dA (u : ℕ) : ℕ → ZMod 3 := fun l => (dg u (8 + l) : ZMod 3)

theorem pR_succ (g : ℕ → G) (m : ℕ) (v : ℕ → ZMod 3) :
    pR g (m + 1) v = pR g m v * g m ^ (v m).val := by
  simp [pR, List.range_succ]

theorem pow_mod3 {g : G} (hg : g ^ 3 = 1) (p : ℕ) : g ^ (p % 3) = g ^ p := by
  conv_rhs => rw [← Nat.div_add_mod p 3, pow_add, pow_mul, hg, one_pow, one_mul]

theorem pow_val_add {g : G} (hg : g ^ 3 = 1) (a b : ZMod 3) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, pow_mod3 hg, pow_add]

theorem pR_add {g : ℕ → G} : ∀ {m : ℕ}, (∀ l < m, g l ^ 3 = 1) →
    (∀ l < m, ∀ l' < m, Commute (g l) (g l')) → ∀ v w, pR g m (v + w) = pR g m v * pR g m w
  | 0, _, _, v, w => by simp [pR]
  | m + 1, h3, hc, v, w => by
    have ih := pR_add (m := m) (fun l hl => h3 l (by omega))
      (fun l hl l' hl' => hc l (by omega) l' (by omega)) v w
    have hcm : Commute (pR g m w) (g m ^ (v m).val) := by
      apply Commute.list_prod_left
      intro z hz
      simp only [List.mem_map, List.mem_range] at hz
      obtain ⟨l, hl, rfl⟩ := hz
      exact (hc l (by omega) m (by omega)).pow_pow _ _
    rw [pR_succ, pR_succ, pR_succ, ih, Pi.add_apply, pow_val_add (h3 m (by omega)), mul_assoc,
      ← mul_assoc (pR g m w), hcm.eq]
    simp only [mul_assoc]

theorem pR_zero (g : ℕ → G) (m : ℕ) : pR g m 0 = 1 := by simp [pR]

theorem pR_congr (g : ℕ → G) (m : ℕ) {v w : ℕ → ZMod 3} (h : ∀ l < m, v l = w l) :
    pR g m v = pR g m w := by
  unfold pR
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [h l (List.mem_range.1 hl)]

structure ElemAb (x : ℕ → G) : Prop where
  cube : ∀ l < 5, x (8 + l) ^ 3 = 1
  comm : ∀ l < 5, ∀ l' < 5, Commute (x (8 + l)) (x (8 + l'))

theorem aEl_add {x : ℕ → G} (hA : ElemAb x) (v w : ℕ → ZMod 3) :
    aEl x (v + w) = aEl x v * aEl x w := pR_add hA.cube hA.comm v w

theorem aEl_neg {x : ℕ → G} (hA : ElemAb x) (v : ℕ → ZMod 3) : aEl x (-v) = (aEl x v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← aEl_add hA, neg_add_cancel]
  exact pR_zero _ _

theorem aEl_nsmul {x : ℕ → G} (hA : ElemAb x) (v : ℕ → ZMod 3) :
    ∀ n : ℕ, aEl x (n • v) = aEl x v ^ n
  | 0 => by simp [aEl, pR_zero]
  | n + 1 => by rw [succ_nsmul, aEl_add hA, aEl_nsmul hA v n, pow_succ]

theorem aEl_sum {x : ℕ → G} (hA : ElemAb x) :
    ∀ L : List (ℕ → ZMod 3), aEl x L.sum = (L.map (aEl x)).prod
  | [] => by simp [aEl, pR_zero]
  | a :: L => by rw [List.sum_cons, aEl_add hA, aEl_sum hA L, List.map_cons, List.prod_cons]

theorem list_sum_apply (L : List (ℕ → ZMod 3)) (k : ℕ) : L.sum k = (L.map fun f => f k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem conj_aEl {x : ℕ → G} (hA : ElemAb x) {r : G} {μ : ℕ → ℕ → ZMod 3}
    (hr : ∀ l < 5, r⁻¹ * x (8 + l) * r = aEl x (μ l)) (v : ℕ → ZMod 3) :
    r⁻¹ * aEl x v * r = aEl x fun k => ((List.range 5).map fun l => v l * μ l k).sum := by
  have e : r⁻¹ * aEl x v * r = MulAut.conj r⁻¹ (aEl x v) := by
    rw [MulAut.conj_apply, inv_inv]
  rw [e, aEl, pR, map_list_prod, List.map_map]
  have e2 : (List.range 5).map ((MulAut.conj r⁻¹) ∘ fun l => x (8 + l) ^ (v l).val) =
      ((List.range 5).map fun l => (v l).val • μ l).map (aEl x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro l hl
    simp only [Function.comp_apply, map_pow, MulAut.conj_apply, inv_inv]
    rw [hr l (List.mem_range.1 hl), aEl_nsmul hA]
  rw [e2, ← aEl_sum hA]
  congr 1
  funext k
  rw [list_sum_apply, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp [nsmul_eq_mul]

@[expose] def CG (x : ℕ → G) (g : G) : Prop := ∀ v, ∃ w, g⁻¹ * aEl x v * g = aEl x w

theorem CG_one (x : ℕ → G) : CG x 1 := fun v => ⟨v, by simp⟩

theorem CG_mul {x : ℕ → G} {a b : G} (ha : CG x a) (hb : CG x b) : CG x (a * b) := fun v => by
  obtain ⟨w, hw⟩ := ha v
  obtain ⟨w', hw'⟩ := hb w
  refine ⟨w', ?_⟩
  rw [← hw', ← hw]
  group

theorem CG_pow {x : ℕ → G} {a : G} (ha : CG x a) : ∀ n : ℕ, CG x (a ^ n)
  | 0 => by simpa using CG_one x
  | n + 1 => by rw [pow_succ]; exact CG_mul (CG_pow ha n) ha

theorem CG_prod {x : ℕ → G} : ∀ L : List G, (∀ g ∈ L, CG x g) → CG x L.prod
  | [], _ => by simpa using CG_one x
  | a :: L, h => by
    rw [List.prod_cons]
    exact CG_mul (h a (by simp)) (CG_prod L fun g hg => h g (by simp [hg]))

@[expose] def NormA (x : ℕ → G) : Prop :=
  ∀ k < 13, ∀ l < 5, ∃ μ, (x k)⁻¹ * x (8 + l) * x k = aEl x μ

theorem CG_nv {x : ℕ → G} (hA : ElemAb x) (hN : NormA x) (u : ℕ) : CG x (nv x 13 u) := by
  apply CG_prod
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  apply CG_pow
  intro v
  choose μ hμ using hN k hk
  exact ⟨_, conj_aEl hA (μ := fun l => if h : l < 5 then μ l h else 0)
    (fun l hl => by simp only [dif_pos hl]; exact hμ l hl) v⟩

theorem nv_split (x : ℕ → G) (v : ℕ) :
    nv x 13 v = ((List.range 8).map fun k => x k ^ dg v k).prod *
      ((List.range 5).map fun l => x (8 + l) ^ dg v (8 + l)).prod := by
  unfold nv
  rw [show 13 = 8 + 5 from rfl, List.range_add, List.map_append, List.prod_append, List.map_map]
  rfl

theorem tail_aEl (x : ℕ → G) {v : ℕ} (hd : ∀ k, dg v k < 3) :
    ((List.range 5).map fun l => x (8 + l) ^ dg v (8 + l)).prod = aEl x (dA v) := by
  unfold aEl pR dA
  congr 1
  apply List.map_congr_left
  intro l _
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hd _)]

theorem low_one (x : ℕ → G) {v : ℕ} (hd : ∀ k < 8, dg v k = 0) :
    ((List.range 8).map fun k => x k ^ dg v k).prod = 1 := by
  rw [List.map_congr_left (g := fun _ => (1 : G))]
  · simp
  · intro k hk
    rw [hd k (List.mem_range.1 hk), pow_zero]

theorem aOK_parts {v : ℕ} (h : aOK v = true) : vecOK 13 v = true ∧ ∀ k < 8, dg v k = 0 := by
  obtain ⟨h1, h2⟩ := band_true h
  refine ⟨h1, fun k hk => ?_⟩
  have hl : v % 4 ^ 8 = 0 := by
    have := Nat.eq_of_beq_eq_true h2
    change v &&& ((1 <<< (8 <<< 1)) - 1) = 0 at this
    rw [Nat.shiftLeft_eq, one_mul, pow4, show (4 : ℕ) ^ 8 = 2 ^ 16 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hl
  rw [dg_eq, show (4 : ℕ) ^ 8 = 4 ^ k * (4 * 4 ^ (7 - k)) by
      rw [← pow_succ', ← pow_add]; congr 1; omega,
    mul_assoc, Nat.mul_div_cancel_left _ (by positivity), mul_assoc, Nat.mul_mod_right]

theorem nv_aOK (x : ℕ → G) {v : ℕ} (h : aOK v = true) : nv x 13 v = aEl x (dA v) := by
  obtain ⟨h1, h2⟩ := aOK_parts h
  rw [nv_split, low_one x h2, one_mul, tail_aEl x (vecOK_dg h1)]

@[expose] noncomputable def fromD (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => dg u 0 + 3 * fromD (u / 4) m

theorem dg_div4 (u k : ℕ) : dg (u / 4) k = dg u (k + 1) := by
  rw [dg_eq, dg_eq, Nat.div_div_eq_div_mul, pow_succ']

theorem fromD_spec :
    ∀ m u, (∀ k, dg u k < 3) → fromD u m < 3 ^ m ∧ ∀ k < m, d3 (fromD u m) k = dg u k
  | 0, u, _ => ⟨by simp [fromD], fun k hk => absurd hk (by omega)⟩
  | m + 1, u, hd => by
    obtain ⟨h1, h2⟩ := fromD_spec m (u / 4) fun k => by rw [dg_div4]; exact hd _
    have h0 := hd 0
    refine ⟨by rw [fromD, pow_succ]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [fromD, d3_eq]
      simp
      omega
    · rw [fromD, ← d3_div, show (dg u 0 + 3 * fromD (u / 4) m) / 3 = fromD (u / 4) m by omega,
        h2 k (by omega), dg_div4]

theorem nv_coset (x : ℕ → G) {u : ℕ} (hd : ∀ k, dg u k < 3) :
    fromD u 8 < 6561 ∧ nv x 13 u = nv x 13 (b3v 8 2 (fromD u 8)) * aEl x (dA u) := by
  obtain ⟨h1, h2⟩ := fromD_spec 8 u hd
  refine ⟨h1, ?_⟩
  have hb : ∀ k, dg (b3v 8 2 (fromD u 8)) k = if k < 8 then dg u k else 0 := fun k => by
    rw [b3v2]
    by_cases hk : k < 8
    · rw [if_pos hk, if_pos hk, h2 k hk]
    · rw [if_neg hk, if_neg hk]
  generalize b3v 8 2 (fromD u 8) = T at hb ⊢
  have e1 : ((List.range 5).map fun l => x (8 + l) ^ dg T (8 + l)).prod = 1 := by
    rw [List.map_congr_left (g := fun _ => (1 : G))]
    · simp
    · intro l _
      rw [hb, if_neg (by omega), pow_zero]
  have e2 : ((List.range 8).map fun k => x k ^ dg T k) =
      ((List.range 8).map fun k => x k ^ dg u k) :=
    List.map_congr_left fun k hk => by rw [hb, if_pos (List.mem_range.1 hk)]
  rw [nv_split x u, nv_split x T, tail_aEl x hd, e1, mul_one, e2]

@[expose] def EqHRep (H : ℕ → ℕ) (x : ℕ → G) : Prop :=
  ∀ u v : List ℕ, (∀ c ∈ u, c < 13) → (∀ c ∈ v, c < 13) → (eqH H u v = true ↔ wd x u = wd x v)

theorem cosChk_spec {H : ℕ → ℕ} {RV nR i D : ℕ} (h : cosChk H RV nR i D = true) {t : ℕ}
    (ht : t / 64 = i) (ht' : t < 6561) : ∃ b α ρ, ρ < nR ∧ aOK α = true ∧ vecOK 13 b = true ∧
      eqH H (nwR 13 (b3v 8 2 t) ++ nwR 13 b) (nwR 13 b ++ (nwR 13 (f16 RV ρ) ++ nwR 13 α)) =
        true := by
  unfold cosChk at h
  have key := PK.allN_iff.1 h (t % 64) (Nat.mod_lt _ (by norm_num))
  have et : Nat.add (Nat.shiftLeft i (nat_lit 6)) (t % 64) = t := by
    subst ht
    change (t / 64) <<< 6 + t % 64 = t
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt t (nat_lit 6561) = true := by
    rw [Nat.blt_eq]
    exact ht'
  rw [PK.strictB_eq, et, hb] at key
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at key
  exact ⟨_, _, _, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

theorem clsChk_spec {H : ℕ → ℕ} {CR nQ r c e : ℕ} (h : clsChk H CR nQ r c e = true)
    (h3 : eqH H ((nwR 13 r ++ nwR 13 c) ++ ((nwR 13 r ++ nwR 13 c) ++ (nwR 13 r ++ nwR 13 c))) [] =
      true)
    (h1 : eqH H (nwR 13 r ++ nwR 13 c) [] = false) : ∃ w q, q < nQ ∧ vecOK 13 w = true ∧
      eqH H ((nwR 13 r ++ nwR 13 c) ++ nwR 13 w) (nwR 13 w ++ nwR 13 (f32 CR q)) = true := by
  unfold clsChk at h
  change Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) _ true
    (eqH H (nwR 13 r ++ nwR 13 c) [])) (eqH H ((nwR 13 r ++ nwR 13 c) ++
      ((nwR 13 r ++ nwR 13 c) ++ (nwR 13 r ++ nwR 13 c))) []) = true at h
  rw [h3, h1] at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨_, _, h.1, h.2.1, h.2.2⟩

theorem repChk_spec {H : ℕ → ℕ} {RV CR nQ ρ MV ncl CV WD XD : ℕ}
    (h : repChk H RV CR nQ ρ MV ncl CV WD XD = true) :
    vecOK 13 (f16 RV ρ) = true ∧
    (∀ k < 5, aOK (f32 MV k) = true ∧
      eqH H ((8 + k) :: nwR 13 (f16 RV ρ)) (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 MV k)) = true) ∧
    (∀ a < 243, ∃ b < 243, ∃ j < ncl,
      nAdd (nAdd (b3v 5 4 a) (b3v 5 4 b)) (nSc 2 (mulM MV b)) = nibA (f32 CV j)) ∧
    (∀ j < ncl, aOK (f32 CV j) = true ∧
      clsChk H CR nQ (f16 RV ρ) (f32 CV j) (f64 XD j) = true) := by
  unfold repChk at h
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, Nat.blt_eq] at h
  obtain ⟨hr, hm, hw, hc⟩ := h
  exact ⟨hr, fun k hk => hm k hk, fun a ha =>
    ⟨_, (hw a ha).1, _, (hw a ha).2.1, Nat.eq_of_beq_eq_true (hw a ha).2.2⟩, fun j hj => hc j hj⟩

section Sound

variable {x : ℕ → G} {H : ℕ → ℕ}

theorem eqH_wd (hE : EqHRep H x) {u v : List ℕ} (hu : ∀ c ∈ u, c < 13) (hv : ∀ c ∈ v, c < 13)
    (h : eqH H u v = true) : wd x u = wd x v := (hE u v hu hv).1 h

theorem allLt_append {u v : List ℕ} (hu : ∀ c ∈ u, c < 13) (hv : ∀ c ∈ v, c < 13) :
    ∀ c ∈ u ++ v, c < 13 := fun c hc => by
  rcases List.mem_append.1 hc with h | h
  · exact hu c h
  · exact hv c h

theorem coset_conj (hE : EqHRep H x) {RV nR : ℕ}
    (hR : ∀ ρ < nR, vecOK 13 (f16 RV ρ) = true)
    (hcos : ∀ t < 6561, ∃ D, cosChk H RV nR (t / 64) D = true) {t : ℕ} (ht : t < 6561) :
    ∃ b α ρ, ρ < nR ∧ aOK α = true ∧ vecOK 13 b = true ∧
      (nv x 13 b)⁻¹ * nv x 13 (b3v 8 2 t) * nv x 13 b = nv x 13 (f16 RV ρ) * nv x 13 α := by
  obtain ⟨D, hD⟩ := hcos t ht
  obtain ⟨b, α, ρ, hρ, hα, hb, he⟩ := cosChk_spec hD rfl ht
  have hdT : ∀ k, dg (b3v 8 2 t) k < 3 := fun k => by
    rw [b3v2]
    split
    · exact d3_lt _ _
    · omega
  obtain ⟨T1, T2⟩ := nwR_spec x hdT
  obtain ⟨B1, B2⟩ := nwR_spec x (vecOK_dg hb)
  obtain ⟨R1, R2⟩ := nwR_spec x (vecOK_dg (hR ρ hρ))
  obtain ⟨A1, A2⟩ := nwR_spec x (vecOK_dg (aOK_parts hα).1)
  have e := eqH_wd hE (allLt_append T2 B2) (allLt_append B2 (allLt_append R2 A2)) he
  rw [wd_append, wd_append, wd_append, T1, B1, R1, A1] at e
  refine ⟨b, α, ρ, hρ, hα, hb, ?_⟩
  rw [mul_assoc, e]
  group

@[expose] noncomputable def encD (v : ℕ → ZMod 3) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (v 0).val + 3 * encD (fun k => v (k + 1)) m

theorem encD_spec : ∀ m (v : ℕ → ZMod 3), encD v m < 3 ^ m ∧ ∀ k < m, d3 (encD v m) k = (v k).val
  | 0, v => ⟨by simp [encD], fun k hk => absurd hk (by omega)⟩
  | m + 1, v => by
    obtain ⟨h1, h2⟩ := encD_spec m fun k => v (k + 1)
    have h0 : (v 0).val < 3 := ZMod.val_lt _
    refine ⟨by rw [encD, pow_succ]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [encD, d3_eq]
      simp
      omega
    · have e : ((v 0).val + 3 * encD (fun k => v (k + 1)) m) / 3 = encD (fun k => v (k + 1)) m := by
        omega
      rw [encD, ← d3_div, e, h2 k (by omega)]

theorem list_prod_mem {S : Subgroup G} : ∀ L : List G, (∀ g ∈ L, g ∈ S) → L.prod ∈ S
  | [], _ => by simpa using S.one_mem
  | a :: L, h => by
    rw [List.prod_cons]
    exact S.mul_mem (h a (by simp)) (list_prod_mem L fun g hg => h g (by simp [hg]))

theorem nv_mem (x : ℕ → G) (u : ℕ) : nv x 13 u ∈ Subgroup.closure (x '' Set.Iio 13) := by
  apply list_prod_mem
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem x (Set.mem_Iio.2 hk))) _

theorem aEl_mem (x : ℕ → G) (v : ℕ → ZMod 3) : aEl x v ∈ Subgroup.closure (x '' Set.Iio 13) := by
  apply list_prod_mem
  intro g hg
  simp only [List.mem_map, List.mem_range] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  have hl' : 8 + l < 13 := by omega
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem x (Set.mem_Iio.2 hl'))) _

theorem conj_pow3 (g y : G) : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
  rw [pow_three, pow_three]
  group

theorem order3_conj (hE : EqHRep H x) (hA : ElemAb x) (hN : NormA x) {RV CR nR nQ : ℕ}
    (hCR : ∀ q < nQ, vecOK 13 (f32 CR q) = true)
    (hcos : ∀ t < 6561, ∃ D, cosChk H RV nR (t / 64) D = true)
    (hrep : ∀ ρ < nR, ∃ MV ncl CV WD XD, repChk H RV CR nQ ρ MV ncl CV WD XD = true)
    {u : ℕ} (hu : vecOK 13 u = true) (h3 : nv x 13 u ^ 3 = 1) (h1 : nv x 13 u ≠ 1) :
    ∃ q < nQ, ∃ g ∈ Subgroup.closure (x '' Set.Iio 13),
      g⁻¹ * nv x 13 u * g = nv x 13 (f32 CR q) := by
  have hR : ∀ ρ < nR, vecOK 13 (f16 RV ρ) = true := fun ρ hρ => by
    obtain ⟨MV, ncl, CV, WD, XD, h⟩ := hrep ρ hρ
    exact (repChk_spec h).1
  obtain ⟨ht, hy⟩ := nv_coset x (vecOK_dg hu)
  obtain ⟨b, α, ρ, hρ, hα, hb, hc⟩ := coset_conj hE hR hcos ht
  obtain ⟨v', hv'⟩ := CG_nv hA hN b (dA u)
  have e1 : (nv x 13 b)⁻¹ * nv x 13 u * nv x 13 b = nv x 13 (f16 RV ρ) * aEl x (dA α + v') := by
    calc (nv x 13 b)⁻¹ * nv x 13 u * nv x 13 b
        = ((nv x 13 b)⁻¹ * nv x 13 (b3v 8 2 (fromD u 8)) * nv x 13 b) *
          ((nv x 13 b)⁻¹ * aEl x (dA u) * nv x 13 b) := by rw [hy]; group
      _ = nv x 13 (f16 RV ρ) * aEl x (dA α + v') := by
          rw [hc, hv', aEl_add hA, ← nv_aOK x hα, mul_assoc]
  obtain ⟨MV, ncl, CV, WD, XD, hrc⟩ := hrep ρ hρ
  obtain ⟨hr, hm, hw, hcl⟩ := repChk_spec hrc
  obtain ⟨R1, R2⟩ := nwR_spec x (vecOK_dg hr)
  have hμ : ∀ l < 5, (nv x 13 (f16 RV ρ))⁻¹ * x (8 + l) * nv x 13 (f16 RV ρ) =
      aEl x (dA (f32 MV l)) := by
    intro l hl
    obtain ⟨hmA, hmE⟩ := hm l hl
    obtain ⟨M1, M2⟩ := nwR_spec x (vecOK_dg (aOK_parts hmA).1)
    have hl' : ∀ c ∈ (8 + l) :: nwR 13 (f16 RV ρ), c < 13 := fun c hc => by
      rcases List.mem_cons.1 hc with h | h
      · omega
      · exact R2 c h
    have e := eqH_wd hE hl' (allLt_append R2 M2) hmE
    rw [wd_cons, wd_append, R1, M1] at e
    rw [← nv_aOK x hmA, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨ha, hda⟩ := encD_spec 5 (dA α + v')
  obtain ⟨b', -, j, hj, heq⟩ := hw _ ha
  rw [mulM_eq] at heq
  have hMV : ∀ l < 5, vecOK 13 (f32 MV l) = true := fun l hl => (aOK_parts (hm l hl).1).1
  obtain ⟨gM, hM⟩ := mulMR_spec (b := b') hMV 5 le_rfl
  obtain ⟨g4a, h4a⟩ := b3v4 5 (encD (dA α + v') 5)
  obtain ⟨g4b, h4b⟩ := b3v4 5 b'
  obtain ⟨gS, hS⟩ := nSc_spec (e := 2) (by norm_num) gM
  obtain ⟨gN1, hN1⟩ := nAdd_spec g4a g4b
  obtain ⟨-, hN2⟩ := nAdd_spec gN1 gS
  obtain ⟨hcA, hcls⟩ := hcl j hj
  obtain ⟨-, hC⟩ := nibA_spec (aOK_parts hcA).1
  set w : ℕ → ZMod 3 := fun l => (d3 b' l : ZMod 3) with hw_def
  have key : ∀ k < 5, (dA α + v') k + w k +
      2 * ((List.range 5).map fun l => w l * dA (f32 MV l) k).sum = dA (f32 CV j) k := by
    intro k hk
    have e := congrArg (fun z => (nib z k : ZMod 3)) heq
    rw [hN2 k hk, hN1 k hk, hS k hk, hM k hk, h4a k hk, h4b k hk, hC k hk, hda k hk,
      ZMod.natCast_zmod_val] at e
    push_cast at e
    exact e
  have h2 : (2 : ZMod 3) = -1 := by decide
  have e2 : (aEl x w)⁻¹ * (nv x 13 (f16 RV ρ) * aEl x (dA α + v')) * aEl x w =
      nv x 13 (f16 RV ρ) * nv x 13 (f32 CV j) := by
    have hcj := conj_aEl hA hμ w
    calc (aEl x w)⁻¹ * (nv x 13 (f16 RV ρ) * aEl x (dA α + v')) * aEl x w
        = nv x 13 (f16 RV ρ) * (((nv x 13 (f16 RV ρ))⁻¹ * aEl x w * nv x 13 (f16 RV ρ))⁻¹ *
          aEl x (dA α + v') * aEl x w) := by group
      _ = nv x 13 (f16 RV ρ) * aEl x (-(fun k => ((List.range 5).map fun l =>
          w l * dA (f32 MV l) k).sum) + (dA α + v') + w) := by
          rw [hcj, ← aEl_neg hA, ← aEl_add hA, ← aEl_add hA]
      _ = nv x 13 (f16 RV ρ) * nv x 13 (f32 CV j) := by
          rw [nv_aOK x hcA]
          congr 1
          apply pR_congr
          intro k hk
          rw [← key k hk, h2]
          simp only [Pi.add_apply, Pi.neg_apply]
          ring
  set Z := nv x 13 (f16 RV ρ) * nv x 13 (f32 CV j) with hZ_def
  have hZ : (nv x 13 b * aEl x w)⁻¹ * nv x 13 u * (nv x 13 b * aEl x w) = Z := by
    rw [← e2, ← e1]
    group
  have hZ3 : Z ^ 3 = 1 := by rw [← hZ, conj_pow3, h3]; group
  have hZ1 : Z ≠ 1 := fun h => h1 (by
    have e := hZ
    rw [h] at e
    calc nv x 13 u = (nv x 13 b * aEl x w) * ((nv x 13 b * aEl x w)⁻¹ * nv x 13 u *
        (nv x 13 b * aEl x w)) * (nv x 13 b * aEl x w)⁻¹ := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨C1, C2⟩ := nwR_spec x (vecOK_dg (aOK_parts hcA).1)
  have hX : wd x (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 CV j)) = Z := by rw [wd_append, R1, C1]
  have LX := allLt_append R2 C2
  have hnil : ∀ c ∈ ([] : List ℕ), c < 13 := fun c hc => absurd hc (by simp)
  have h3' := (hE _ [] (allLt_append LX (allLt_append LX LX)) hnil).2
    (by rw [wd_append x (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 CV j)),
      wd_append x (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 CV j)), hX, wd_nil, ← pow_three, hZ3])
  have h1' : eqH H (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 CV j)) [] = false :=
    Bool.eq_false_iff.2 fun h => hZ1 (by rw [← hX, eqH_wd hE LX hnil h, wd_nil])
  obtain ⟨W, q, hq, hW, hWe⟩ := clsChk_spec hcls h3' h1'
  obtain ⟨W1, W2⟩ := nwR_spec x (vecOK_dg hW)
  obtain ⟨Q1, Q2⟩ := nwR_spec x (vecOK_dg (hCR q hq))
  have e3 := eqH_wd hE (allLt_append LX W2) (allLt_append W2 Q2) hWe
  rw [wd_append x (nwR 13 (f16 RV ρ) ++ nwR 13 (f32 CV j)), wd_append x (nwR 13 W), hX, W1,
    Q1] at e3
  refine ⟨q, hq, nv x 13 b * aEl x w * nv x 13 W,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (nv_mem x b) (aEl_mem x w)) (nv_mem x W), ?_⟩
  calc (nv x 13 b * aEl x w * nv x 13 W)⁻¹ * nv x 13 u * (nv x 13 b * aEl x w * nv x 13 W)
      = (nv x 13 W)⁻¹ * ((nv x 13 b * aEl x w)⁻¹ * nv x 13 u * (nv x 13 b * aEl x w)) *
        nv x 13 W := by group
    _ = nv x 13 (f32 CR q) := by rw [hZ, mul_assoc, e3, ← mul_assoc, inv_mul_cancel, one_mul]

end Sound

end CFSG.KS.Fi23Q

end
