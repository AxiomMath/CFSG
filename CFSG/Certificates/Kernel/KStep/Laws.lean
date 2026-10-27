module

public import CFSG.Certificates.Kernel.KStep.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.MonsterConv.Perm

open CFSG.KC.Benes (nxor nland nlor nshl nshr nmul nadd nsub ones_eq)

namespace LawAux

theorem tb_hi {x N i : ℕ} (hx : x < 2 ^ N) (hi : N ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem idx_lt {np S b p : ℕ} (hb : b < np) (hp : p < S) : b * S + p < np * S := by
  have : (b + 1) * S ≤ np * S := Nat.mul_le_mul_right _ hb
  rw [Nat.succ_mul] at this
  omega

theorem idx_mod {S b p : ℕ} (hp : p < S) : (b * S + p) % S = p := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

theorem idx_dec {np S i : ℕ} (hi : i < np * S) :
    i / S < np ∧ i % S < S ∧ i = i / S * S + i % S := by
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h
      simp at hi
    · exact h
  refine ⟨(Nat.div_lt_iff_lt_mul hS).2 hi, Nat.mod_lt _ hS, (Nat.div_add_mod' i S).symm⟩

theorem bd_of_testBit {np S x : ℕ} (h : ∀ i, np * S ≤ i → x.testBit i = false) : Bd np S x :=
  Nat.lt_pow_two_of_testBit x h

theorem resPN_eq (np S x p : ℕ) : resPN np S x p =
    ((∑ b ∈ Finset.range np, 2 ^ b * (x.testBit (b * S + p)).toNat : ℕ) : ZMod (2 ^ np - 1)) := by
  unfold resPN
  simp only [Nat.toNat_testBit]

theorem res_move {np S S' x y p q : ℕ}
    (h : ∀ b < np, x.testBit (b * S + p) = y.testBit (b * S' + q)) :
    resPN np S x p = resPN np S' y q := by
  rw [resPN_eq, resPN_eq]
  congr 1
  exact Finset.sum_congr rfl fun b hb => by rw [h b (Finset.mem_range.1 hb)]

theorem res_of_zero {np S x p : ℕ} (h : Zero np S x p) : resPN np S x p = 0 := by
  rw [resPN_eq, Finset.sum_eq_zero, Nat.cast_zero]
  intro b hb
  rw [h b (Finset.mem_range.1 hb)]
  rfl

theorem zero_zero (np S p : ℕ) : Zero np S 0 p := fun _ _ => Nat.zero_testBit _

theorem rep_of_law {np : ℕ} {O : POps} (hO : PLaw np O) {S m : ℕ} (hm : m < 2 ^ S) :
    Benes.Rep S np (O.rep S m) m := by
  intro q
  by_cases hq : q < S * np
  · rw [Nat.mul_comm] at hq
    obtain ⟨h1, h2, h3⟩ := idx_dec hq
    rw [decide_eq_true (by rw [Nat.mul_comm]; exact hq), Bool.true_and, h3,
      hO.rep_testBit hm h1 h2, idx_mod h2]
  · rw [decide_eq_false hq, Bool.false_and]
    exact tb_hi (hO.rep_lt hm) (by rw [Nat.mul_comm]; omega)

end LawAux

open LawAux

variable {np : ℕ} {O : POps}

theorem resPN_zero (np S p : ℕ) : resPN np S 0 p = 0 := res_of_zero (zero_zero np S p)

theorem resPN_congr {S x y p : ℕ} (h : ∀ b < np, x.testBit (b * S + p) = y.testBit (b * S + p)) :
    resPN np S x p = resPN np S y p := by
  rw [resPN_eq, resPN_eq]
  congr 1
  exact Finset.sum_congr rfl fun b hb => by rw [h b (Finset.mem_range.1 hb)]

theorem bd_land {S x y : ℕ} (hx : Bd np S x) : Bd np S (x &&& y) :=
  lt_of_le_of_lt Nat.and_le_left hx

theorem bd_lor {S x y : ℕ} (hx : Bd np S x) (hy : Bd np S y) : Bd np S (x ||| y) :=
  Nat.or_lt_two_pow hx hy

theorem res_land_rep (hO : PLaw np O) {S m x p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    resPN np S (x &&& O.rep S m) p = if m.testBit p then resPN np S x p else 0 := by
  cases hmp : m.testBit p
  · refine res_of_zero fun b hb => ?_
    rw [Nat.testBit_and, hO.rep_testBit hm hb hp, hmp, Bool.and_false]
  · exact resPN_congr fun b hb => by rw [Nat.testBit_and, hO.rep_testBit hm hb hp, hmp, Bool.and_true]

theorem res_lor {S x y p : ℕ} (hp : p < S)
    (h : (∀ b < np, x.testBit (b * S + p) = false) ∨ ∀ b < np, y.testBit (b * S + p) = false) :
    resPN np S (x ||| y) p = resPN np S x p + resPN np S y p := by
  rcases h with h | h
  · rw [res_of_zero h, zero_add]
    exact resPN_congr fun b hb => by rw [Nat.testBit_or, h b hb, Bool.false_or]
  · rw [res_of_zero h, add_zero]
    exact resPN_congr fun b hb => by rw [Nat.testBit_or, h b hb, Bool.or_false]

theorem res_dsw_rep (hO : PLaw np O) {S d m x p : ℕ} (hv : Benes.ValidIn S d m) (hx : Bd np S x)
    (hp : p < S) :
    resPN np S (dsw d (O.rep S m) x) p = resPN np S x (Benes.swp d m p) := by
  have hR := rep_of_law hO (Benes.lt_of_validIn hv)
  refine res_move fun b hb => ?_
  rw [Benes.testBit_dsw (Benes.rep_disj hR hv), Nat.mul_comm b S, Benes.swp_rep hR hv hb hp]

theorem bd_dsw_rep (hO : PLaw np O) {S d m x : ℕ} (hv : Benes.ValidIn S d m) (hx : Bd np S x) :
    Bd np S (dsw d (O.rep S m) x) := by
  have hR := rep_of_law hO (Benes.lt_of_validIn hv)
  refine bd_of_testBit fun i hi => ?_
  rw [Benes.testBit_dsw (Benes.rep_disj hR hv), Benes.swp_rep_hi hR hv (by rw [Nat.mul_comm]; exact hi)]
  exact tb_hi hx hi

theorem res_shr_land (hO : PLaw np O) {S o m x p : ℕ} (ho : o ≤ S) (hm : m < 2 ^ (S - o))
    (hx : Bd np S x) (hp : p < S) :
    resPN np S ((x >>> o) &&& O.rep S m) p = if m.testBit p then resPN np S x (p + o) else 0 := by
  have hm' : m < 2 ^ S := Benes.lt_two_pow_mono hm (by omega)
  rw [res_land_rep hO hm' hp]
  cases hmp : m.testBit p
  · rfl
  · have hpo : p < S - o := by
      by_contra hc
      rw [tb_hi hm (by omega)] at hmp
      exact absurd hmp (by decide)
    exact res_move fun b hb => by rw [Nat.testBit_shiftRight]; congr 1; omega

namespace LawAux

theorem testBit_shl_pl {np S o x b p : ℕ} (hx : Bd np S x)
    (hs : ∀ b < np, ∀ q < S, S - o ≤ q → x.testBit (b * S + q) = false) (hb : b < np) (hp : p < S) :
    (x <<< o).testBit (b * S + p) = if o ≤ p then x.testBit (b * S + (p - o)) else false := by
  rw [Nat.testBit_shiftLeft]
  split_ifs with h
  · rw [decide_eq_true (by omega), Bool.true_and]
    congr 1
    omega
  · by_cases h2 : b * S + p < o
    · rw [decide_eq_false (by omega), Bool.false_and]
    · rw [decide_eq_true (by omega), Bool.true_and]
      have hi : b * S + p - o < np * S := by have := idx_lt hb hp; omega
      obtain ⟨c1, c2, c3⟩ := idx_dec hi
      have hr : S - o ≤ (b * S + p - o) % S := by
        by_cases hc : b ≤ (b * S + p - o) / S
        · have := Nat.mul_le_mul_right S hc
          omega
        · have := Nat.mul_le_mul_right S (by omega : (b * S + p - o) / S + 1 ≤ b)
          rw [Nat.succ_mul] at this
          omega
      rw [c3]
      exact hs _ c1 _ c2 hr

end LawAux

theorem res_shl {S o x p : ℕ} (hx : Bd np S x)
    (hs : ∀ b < np, ∀ q < S, S - o ≤ q → x.testBit (b * S + q) = false) (hp : p < S) :
    resPN np S (x <<< o) p = if o ≤ p then resPN np S x (p - o) else 0 := by
  split_ifs with h
  · exact res_move fun b hb => by simp only [testBit_shl_pl hx hs hb hp, h, ↓reduceIte]
  · exact res_of_zero fun b hb => by simp only [testBit_shl_pl hx hs hb hp, h, ↓reduceIte]

theorem bd_shl {S o x : ℕ} (hx : Bd np S x)
    (hs : ∀ b < np, ∀ q < S, S - o ≤ q → x.testBit (b * S + q) = false) : Bd np S (x <<< o) := by
  refine bd_of_testBit fun i hi => ?_
  rw [Nat.testBit_shiftLeft]
  by_cases h1 : o ≤ i
  · rw [decide_eq_true h1, Bool.true_and]
    by_cases h2 : np * S ≤ i - o
    · exact tb_hi hx h2
    · obtain ⟨c1, c2, c3⟩ := idx_dec (by omega : i - o < np * S)
      have := Nat.mul_le_mul_right S (by omega : (i - o) / S + 1 ≤ np)
      rw [Nat.succ_mul] at this
      rw [c3]
      exact hs _ c1 _ c2 (by omega)
  · rw [decide_eq_false h1, Bool.false_and]

namespace LawAux

theorem repN_Rep {S m : ℕ} (hm : m < 2 ^ S) (n : ℕ) : Benes.Rep S n (repN S n m) m :=
  Benes.rep_repP (fun p hp => by
    by_contra h
    rw [tb_hi hm (by omega)] at hp
    exact absurd hp (by decide)) n

theorem testBit_repN {S n m b p : ℕ} (hm : m < 2 ^ S) (hb : b < n) (hp : p < S) :
    (repN S n m).testBit (b * S + p) = m.testBit p := by
  rw [repN_Rep hm n, idx_mod hp, decide_eq_true (by rw [Nat.mul_comm S n]; exact idx_lt hb hp),
    Bool.true_and]

theorem repN_lt {S n m : ℕ} (hm : m < 2 ^ S) : repN S n m < 2 ^ (n * S) :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [repN_Rep hm n, decide_eq_false (by rw [Nat.mul_comm S n]; omega), Bool.false_and]

theorem testBit_mN {S n i : ℕ} : (mN S n).testBit i = decide (i < n * S) := by
  rw [mN, ones_eq, nmul, Nat.testBit_two_pow_sub_one]

theorem mN_eq (S n : ℕ) : mN S n = 2 ^ (n * S) - 1 := by rw [mN, ones_eq, nmul]

theorem rotN_lt (S n k x : ℕ) : rotN S n k x < 2 ^ (n * S) := by
  unfold rotN
  rw [mN_eq, nland]
  exact Benes.land_ones_lt _ _

theorem testBit_rotN {S n k x b p : ℕ} (hk : k ≤ n) (hx : x < 2 ^ (n * S)) (hb : b < n)
    (hp : p < S) :
    (rotN S n k x).testBit (b * S + p) = x.testBit (((b + n - k) % n) * S + p) := by
  unfold rotN
  rw [mN_eq]
  simp only [nland, nlor, nshl, nshr, nmul, nsub, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  rw [decide_eq_true (idx_lt hb hp), Bool.and_true]
  by_cases hkb : k ≤ b
  · have e1 : (b + n - k) % n = b - k := by
      rw [show b + n - k = (b - k) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have m1 : k * S ≤ b * S := Nat.mul_le_mul_right _ hkb
    have m2 : (b - k) * S + k * S = b * S := by rw [← Nat.add_mul, Nat.sub_add_cancel hkb]
    have m3 : (n - k) * S + b * S = (b - k) * S + n * S := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    rw [e1, decide_eq_true (by omega), Bool.true_and,
      tb_hi hx (by omega : n * S ≤ (n - k) * S + (b * S + p)), Bool.or_false]
    congr 1
    omega
  · have e1 : (b + n - k) % n = b + n - k := Nat.mod_eq_of_lt (by omega)
    have m1 : (b + 1) * S ≤ k * S := Nat.mul_le_mul_right _ (by omega)
    have m3 : (n - k) * S + b * S = (b + n - k) * S := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [Nat.succ_mul] at m1
    rw [e1, decide_eq_false (by omega), Bool.false_and, Bool.false_or]
    congr 1
    omega

@[expose] def pf (n S x p : ℕ) (k : ZMod n) : Bool := x.testBit (k.val * S + p)

@[expose] def vv (n : ℕ) (f : ZMod n → Bool) : ℕ := ∑ b ∈ Finset.range n, 2 ^ b * (f b).toNat

theorem resPN_vv (n S x p : ℕ) : resPN n S x p = (vv n (pf n S x p) : ZMod (2 ^ n - 1)) := by
  rw [resPN_eq, vv]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [pf, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]

theorem two_pow_one (n : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have h := ZMod.natCast_self (2 ^ n - 1)
  have e : (2 ^ n - 1 : ℕ) + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
  calc (2 : ZMod (2 ^ n - 1)) ^ n = ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) := by push_cast; rfl
    _ = (((2 ^ n - 1 : ℕ) + 1 : ℕ) : ZMod (2 ^ n - 1)) := by rw [e]
    _ = 1 := by rw [Nat.cast_add, h, zero_add, Nat.cast_one]

theorem two_pow_mod (n a : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ (a % n) = 2 ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, two_pow_one, one_pow, one_mul]

theorem geom2 : ∀ n : ℕ, ∑ b ∈ Finset.range n, 2 ^ b + 1 = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := geom2 n
    omega

theorem vv_not (n : ℕ) (f : ZMod n → Bool) :
    (vv n (fun k => !f k) : ZMod (2 ^ n - 1)) = -(vv n f : ZMod (2 ^ n - 1)) := by
  have h : vv n (fun k => !f k) + vv n f + 1 = 2 ^ n := by
    rw [← geom2 n, vv, vv, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    cases f b <;> simp
  have h' := congrArg (Nat.cast : ℕ → ZMod (2 ^ n - 1)) h
  push_cast at h'
  rw [two_pow_one] at h'
  exact eq_neg_of_add_eq_zero_left (add_eq_right.1 h')

variable {n : ℕ} [NeZero n]

theorem vv_rot1 (f : ZMod n → Bool) :
    (vv n (fun k => f (k - 1)) : ZMod (2 ^ n - 1)) = 2 * (vv n f : ZMod (2 ^ n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  have hm : ((m : ℕ) : ZMod (m + 1)) = -1 := by
    have := ZMod.natCast_self (m + 1)
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have e1 : ∀ b : ℕ, ((b + 1 : ℕ) : ZMod (m + 1)) - 1 = b := by
    intro b
    push_cast
    ring
  have e2 : ((0 : ℕ) : ZMod (m + 1)) - 1 = m := by rw [hm, Nat.cast_zero, zero_sub]
  have h2 := two_pow_one (m + 1)
  unfold vv
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [e1, e2]
  push_cast
  rw [mul_add, Finset.mul_sum, one_mul, ← mul_assoc, ← pow_succ', h2, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem vv_rot (f : ZMod n → Bool) : ∀ k : ℕ,
    (vv n (fun j => f (j - k)) : ZMod (2 ^ n - 1)) = 2 ^ k * (vv n f : ZMod (2 ^ n - 1))
  | 0 => by simp
  | k + 1 => by
    have e : (fun j => f (j - ((k + 1 : ℕ) : ZMod n))) = fun j => (fun j' => f (j' - k)) (j - 1) := by
      funext j
      congr 1
      push_cast
      ring
    rw [e, vv_rot1 (fun j' : ZMod n => f (j' - k)), vv_rot f k, pow_succ]
    ring

theorem pf_rotN {S k x p : ℕ} (hk : k ≤ n) (hx : x < 2 ^ (n * S)) (hp : p < S) (j : ZMod n) :
    pf n S (rotN S n k x) p j = pf n S x p (j - k) := by
  unfold pf
  rw [testBit_rotN hk hx (ZMod.val_lt j) hp]
  have e : (j - (k : ZMod n)) = ((j.val + n - k : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self]
    ring
  rw [e, ZMod.val_natCast]

theorem res_rotN {S k x p : ℕ} (hk : k ≤ n) (hx : x < 2 ^ (n * S)) (hp : p < S) :
    resPN n S (rotN S n k x) p = 2 ^ k * resPN n S x p := by
  rw [resPN_vv, resPN_vv]
  have e : pf n S (rotN S n k x) p = fun j => pf n S x p (j - k) := funext (pf_rotN hk hx hp)
  rw [e, vv_rot]

theorem zero_iff {S x p : ℕ} : Zero n S x p ↔ ∀ k : ZMod n, pf n S x p k = false := by
  constructor
  · intro h k
    exact h _ (ZMod.val_lt k)
  · intro h b hb
    have := h b
    rwa [pf, ZMod.val_natCast, Nat.mod_eq_of_lt hb] at this

theorem pf_xor (S x y p : ℕ) (k : ZMod n) :
    pf n S (Nat.xor x y) p k = (pf n S x p k ^^ pf n S y p k) := by
  simp only [pf, nxor, Nat.testBit_xor]

theorem pf_and (S x y p : ℕ) (k : ZMod n) :
    pf n S (Nat.land x y) p k = (pf n S x p k && pf n S y p k) := by
  simp only [pf, nland, Nat.testBit_and]

theorem pf_or (S x y p : ℕ) (k : ZMod n) :
    pf n S (Nat.lor x y) p k = (pf n S x p k || pf n S y p k) := by
  simp only [pf, nlor, Nat.testBit_or]

@[expose] noncomputable def kLoop (S n P0 G0 : ℕ) (i : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (G0, P0)
    (fun i ih => Prod.rec (motive := fun _ => Nat × Nat)
      (fun G P => (fun s => strictNP (Nat.lor G (Nat.land P (rotN S n s G)))
          (fun G' => (G', Nat.land P (rotN S n s P))))
        (Nat.mod (Nat.shiftLeft (nat_lit 1) i) n)) ih) i

theorem addN_eq (S n lg x y : ℕ) : addN S n lg x y = Nat.xor (Nat.xor x y)
    (rotN S n (Nat.mod 1 n) (kLoop S n (Nat.xor x y) (Nat.land x y) lg).1) := rfl

theorem strictNP_eq (y : ℕ) (k : ℕ → ℕ × ℕ) : strictNP y k = k y := by cases y <;> rfl

theorem kLoop_succ (S n P0 G0 i : ℕ) : kLoop S n P0 G0 (i + 1) =
    (Nat.lor (kLoop S n P0 G0 i).1 (Nat.land (kLoop S n P0 G0 i).2
        (rotN S n (Nat.mod (Nat.shiftLeft 1 i) n) (kLoop S n P0 G0 i).1)),
      Nat.land (kLoop S n P0 G0 i).2 (rotN S n (Nat.mod (Nat.shiftLeft 1 i) n) (kLoop S n P0 G0 i).2)) := by
  change Prod.rec (motive := fun _ => Nat × Nat)
      (fun G P => (fun s => strictNP (Nat.lor G (Nat.land P (rotN S n s G)))
          (fun G' => (G', Nat.land P (rotN S n s P))))
        (Nat.mod (Nat.shiftLeft (nat_lit 1) i) n)) (kLoop S n P0 G0 i) = _
  generalize kLoop S n P0 G0 i = r
  obtain ⟨G, P⟩ := r
  exact strictNP_eq _ _

theorem gen_step {g q G P : ZMod n → Bool} {L : ℕ}
    (hG : ∀ k, G k = true ↔ ∃ d < L, g (k - d) = true ∧ ∀ e < d, q (k - e) = true)
    (hP : ∀ k, P k = true ↔ ∀ e < L, q (k - e) = true) (k : ZMod n) :
    ((G k || (P k && G (k - (L : ℕ)))) = true ↔
        ∃ d < 2 * L, g (k - d) = true ∧ ∀ e < d, q (k - e) = true) ∧
      ((P k && P (k - (L : ℕ))) = true ↔ ∀ e < 2 * L, q (k - e) = true) := by
  have sh : ∀ a : ℕ, k - (L : ℕ) - (a : ℕ) = k - ((L + a : ℕ) : ZMod n) := by
    intro a
    push_cast
    ring
  constructor
  · simp only [Bool.or_eq_true, Bool.and_eq_true, hG, hP, sh]
    constructor
    · rintro (⟨d, hd, h1, h2⟩ | ⟨h0, d, hd, h1, h2⟩)
      · exact ⟨d, by omega, h1, h2⟩
      · refine ⟨L + d, by omega, h1, fun e he => ?_⟩
        by_cases hel : e < L
        · exact h0 e hel
        · have := h2 (e - L) (by omega)
          rwa [show L + (e - L) = e by omega] at this
    · rintro ⟨d, hd, h1, h2⟩
      by_cases hdl : d < L
      · exact Or.inl ⟨d, hdl, h1, h2⟩
      · refine Or.inr ⟨fun e he => h2 e (by omega), d - L, by omega, ?_, fun e he => ?_⟩
        · rwa [show L + (d - L) = d by omega]
        · exact h2 (L + e) (by omega)
  · simp only [Bool.and_eq_true, hP, sh]
    constructor
    · rintro ⟨h1, h2⟩ e he
      by_cases hel : e < L
      · exact h1 e hel
      · have := h2 (e - L) (by omega)
        rwa [show L + (e - L) = e by omega] at this
    · intro h
      exact ⟨fun e he => h e (by omega), fun e he => h (L + e) (by omega)⟩

theorem cast_shl_mod (i : ℕ) : ((Nat.mod (Nat.shiftLeft 1 i) n : ℕ) : ZMod n) = ((2 ^ i : ℕ) : ZMod n) := by
  change (((1 <<< i) % n : ℕ) : ZMod n) = _
  rw [ZMod.natCast_mod, Nat.shiftLeft_eq, Nat.one_mul]

theorem kLoop_inv {S P0 G0 p : ℕ} {g q : ZMod n → Bool} (hG0 : G0 < 2 ^ (n * S))
    (hP0 : P0 < 2 ^ (n * S)) (hp : p < S) (hg : ∀ k, pf n S G0 p k = g k)
    (hq : ∀ k, pf n S P0 p k = q k) : ∀ i,
    (kLoop S n P0 G0 i).1 < 2 ^ (n * S) ∧ (kLoop S n P0 G0 i).2 < 2 ^ (n * S) ∧
      ∀ k, (pf n S (kLoop S n P0 G0 i).1 p k = true ↔
          ∃ d : ℕ, d < 2 ^ i ∧ g (k - d) = true ∧ ∀ e : ℕ, e < d → q (k - e) = true) ∧
        (pf n S (kLoop S n P0 G0 i).2 p k = true ↔ ∀ e : ℕ, e < 2 ^ i → q (k - e) = true)
  | 0 => by
    refine ⟨hG0, hP0, fun k => ⟨?_, ?_⟩⟩
    · change pf n S G0 p k = true ↔ _
      rw [hg]
      constructor
      · intro h
        exact ⟨0, by decide, by rwa [Nat.cast_zero, sub_zero], fun e he => absurd he (by omega)⟩
      · rintro ⟨d, hd, h1, -⟩
        have : d = 0 := by omega
        subst this
        rwa [Nat.cast_zero, sub_zero] at h1
    · change pf n S P0 p k = true ↔ _
      rw [hq]
      constructor
      · intro h e he
        have : e = 0 := by omega
        subst this
        rwa [Nat.cast_zero, sub_zero]
      · intro h
        have := h 0 (by decide)
        rwa [Nat.cast_zero, sub_zero] at this
  | i + 1 => by
    obtain ⟨b1, b2, ih⟩ := kLoop_inv hG0 hP0 hp hg hq i
    rw [kLoop_succ]
    have hs : Nat.mod (Nat.shiftLeft 1 i) n ≤ n := (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))).le
    refine ⟨Nat.or_lt_two_pow b1 (lt_of_le_of_lt Nat.and_le_left b2),
      lt_of_le_of_lt Nat.and_le_left b2, fun k => ?_⟩
    simp only [pf_or, pf_and, pf_rotN hs b1 hp, pf_rotN hs b2 hp, cast_shl_mod]
    rw [pow_succ, Nat.mul_comm]
    exact gen_step (fun k => (ih k).1) (fun k => (ih k).2) k

theorem carry_rec {g q C : ZMod n → Bool} (hx : ∀ k, (g k && q k) = false) {L : ℕ} (hL : n ≤ L)
    (hC : ∀ j, C j = true ↔ ∃ d < L, g (j - 1 - d) = true ∧ ∀ e < d, q (j - 1 - e) = true)
    (k : ZMod n) : C (k + 1) = (g k || (q k && C k)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have s1 : ∀ a : ℕ, k + 1 - 1 - (a : ℕ) = k - a := by intro a; ring
  have s2 : ∀ a : ℕ, k - 1 - (a : ℕ) = k - ((a + 1 : ℕ) : ZMod n) := by intro a; push_cast; ring
  rw [Bool.eq_iff_iff, hC, Bool.or_eq_true, Bool.and_eq_true, hC]
  simp only [s1, s2]
  constructor
  · rintro ⟨d, hd, h1, h2⟩
    rcases d with _ | d
    · left
      rwa [Nat.cast_zero, sub_zero] at h1
    · right
      refine ⟨by have := h2 0 (by omega); rwa [Nat.cast_zero, sub_zero] at this, ?_⟩
      by_cases hdl : d < L
      · exact ⟨d, hdl, h1, fun e he => h2 (e + 1) (by omega)⟩
      · exfalso
        have hgL := h1
        have hqL := h2 (d + 1 - n) (by omega)
        have e : ((d + 1 - n : ℕ) : ZMod n) = ((d + 1 : ℕ) : ZMod n) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, sub_zero]
        rw [e] at hqL
        have := hx (k - ((d + 1 : ℕ) : ZMod n))
        rw [hgL, hqL] at this
        exact absurd this (by decide)
  · rintro (h | ⟨h0, d, hd, h1, h2⟩)
    · exact ⟨0, by omega, by rwa [Nat.cast_zero, sub_zero], fun e he => absurd he (by omega)⟩
    · by_cases hdl : d + 1 < L
      · refine ⟨d + 1, hdl, h1, fun e he => ?_⟩
        rcases e with _ | e
        · rwa [Nat.cast_zero, sub_zero]
        · exact h2 e (by omega)
      · exfalso
        have hqL : q (k - ((d + 1 - n : ℕ) : ZMod n)) = true := by
          rcases hm : d + 1 - n with _ | e
          · rwa [Nat.cast_zero, sub_zero]
          · exact h2 e (by omega)
        have e : ((d + 1 - n : ℕ) : ZMod n) = ((d + 1 : ℕ) : ZMod n) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, sub_zero]
        rw [e] at hqL
        have := hx (k - ((d + 1 : ℕ) : ZMod n))
        rw [h1, hqL] at this
        exact absurd this (by decide)

theorem lin_aux (P s c a b cc : ℕ) (h : s + 2 * c = a + b + cc) :
    P * s + P * 2 * c = P * a + P * b + P * cc := by
  rw [mul_assoc, ← mul_add, h]
  ring

theorem vv_add {a b c s : ZMod n → Bool} (hs : ∀ k, s k = ((a k ^^ b k) ^^ c k))
    (hc : ∀ k, c (k + 1) = ((a k && b k) || ((a k ^^ b k) && c k))) :
    (vv n s : ZMod (2 ^ n - 1)) = vv n a + vv n b := by
  have hk : ∀ k, (s k).toNat + 2 * (c (k + 1)).toNat = (a k).toNat + (b k).toNat + (c k).toNat := by
    intro k
    rw [hs, hc]
    cases a k <;> cases b k <;> cases c k <;> rfl
  have h1 : vv n s + ∑ i ∈ Finset.range n, 2 ^ (i + 1) * (c ((i + 1 : ℕ) : ZMod n)).toNat =
      vv n a + vv n b + vv n c := by
    unfold vv
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, Nat.cast_succ]
    exact lin_aux _ _ _ _ _ _ (hk i)
  have h2 : ∑ i ∈ Finset.range n, 2 ^ (i + 1) * (c ((i + 1 : ℕ) : ZMod n)).toNat + (c 0).toNat =
      vv n c + 2 ^ n * (c 0).toNat := by
    have e1 := Finset.sum_range_succ' (fun i => 2 ^ i * (c (i : ZMod n)).toNat) n
    have e2 := Finset.sum_range_succ (fun i => 2 ^ i * (c (i : ZMod n)).toNat) n
    rw [ZMod.natCast_self] at e2
    simp only [pow_zero, one_mul, Nat.cast_zero] at e1
    unfold vv
    omega
  have h1' := congrArg (Nat.cast : ℕ → ZMod (2 ^ n - 1)) h1
  have h2' := congrArg (Nat.cast : ℕ → ZMod (2 ^ n - 1)) h2
  push_cast at h1' h2'
  rw [two_pow_one, one_mul] at h2'
  rw [add_right_cancel h2'] at h1'
  exact add_right_cancel h1'

theorem pf_addN {S lg x y p : ℕ} (hlg : n ≤ 2 ^ lg) (hx : x < 2 ^ (n * S)) (hy : y < 2 ^ (n * S))
    (hp : p < S) :
    addN S n lg x y < 2 ^ (n * S) ∧ ∃ C : ZMod n → Bool,
      (∀ k, pf n S (addN S n lg x y) p k = ((pf n S x p k ^^ pf n S y p k) ^^ C k)) ∧
      (∀ k, C (k + 1) = ((pf n S x p k && pf n S y p k) ||
        ((pf n S x p k ^^ pf n S y p k) && C k))) ∧
      ((∀ k, pf n S x p k = false) → (∀ k, pf n S y p k = false) → ∀ k, C k = false) := by
  have hP0 : Nat.xor x y < 2 ^ (n * S) := Nat.xor_lt_two_pow hx hy
  have hG0 : Nat.land x y < 2 ^ (n * S) := lt_of_le_of_lt Nat.and_le_left hx
  obtain ⟨b1, -, hinv⟩ := kLoop_inv (g := fun k => pf n S x p k && pf n S y p k)
    (q := fun k => pf n S x p k ^^ pf n S y p k) hG0 hP0 hp (pf_and S x y p) (pf_xor S x y p) lg
  have h1 : Nat.mod 1 n ≤ n := (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))).le
  have c1 : ((Nat.mod 1 n : ℕ) : ZMod n) = 1 := by
    change ((1 % n : ℕ) : ZMod n) = 1
    rw [ZMod.natCast_mod, Nat.cast_one]
  refine ⟨by rw [addN_eq]; exact Nat.xor_lt_two_pow hP0 (rotN_lt _ _ _ _),
    fun k => pf n S (kLoop S n (Nat.xor x y) (Nat.land x y) lg).1 p (k - 1), fun k => ?_, ?_, ?_⟩
  · rw [addN_eq, pf_xor, pf_xor, pf_rotN h1 b1 hp, c1]
  · refine carry_rec (g := fun k => pf n S x p k && pf n S y p k)
      (q := fun k => pf n S x p k ^^ pf n S y p k) (fun k => ?_) hlg (fun j => (hinv (j - 1)).1)
    cases pf n S x p k <;> cases pf n S y p k <;> rfl
  · intro hx0 hy0 k
    cases h : pf n S (kLoop S n (Nat.xor x y) (Nat.land x y) lg).1 p (k - 1)
    · exact h
    · obtain ⟨d, -, h1, -⟩ := (hinv (k - 1)).1.mp h
      simp only [hx0, Bool.false_and] at h1
      exact absurd h1 (by decide)

theorem nNeg_bd {S m x : ℕ} (hm : m < 2 ^ S) (hx : x < 2 ^ (n * S)) :
    negMN S n m x < 2 ^ (n * S) := Nat.xor_lt_two_pow hx (repN_lt hm)

theorem nNeg_bit {S m x b p : ℕ} (hm : m < 2 ^ S) (hb : b < n) (hp : p < S) :
    (negMN S n m x).testBit (b * S + p) = (x.testBit (b * S + p) ^^ m.testBit p) := by
  rw [negMN, nxor, Nat.testBit_xor, testBit_repN hm hb hp]

theorem nNeg_res {S m x p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    resPN n S (negMN S n m x) p = if m.testBit p then -resPN n S x p else resPN n S x p := by
  cases hmp : m.testBit p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact resPN_congr fun b hb => by rw [nNeg_bit hm hb hp, hmp, Bool.xor_false]
  · simp only [↓reduceIte]
    rw [resPN_vv, resPN_vv]
    have e : pf n S (negMN S n m x) p = fun k => !(pf n S x p k) := funext fun k => by
      unfold pf
      rw [nNeg_bit hm (ZMod.val_lt k) hp, hmp, Bool.xor_true]
    rw [e, vv_not]

theorem nNeg_zero {S m x p : ℕ} (hm : m < 2 ^ S) (hp : p < S) (h0 : m.testBit p = false)
    (hz : Zero n S x p) : Zero n S (negMN S n m x) p := fun b hb => by
  rw [nNeg_bit hm hb hp, hz b hb, h0]
  rfl

theorem nAdd_bd {S lg x y : ℕ} (hx : x < 2 ^ (n * S)) (hy : y < 2 ^ (n * S)) :
    addN S n lg x y < 2 ^ (n * S) := by
  rw [addN_eq]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx hy) (rotN_lt _ _ _ _)

theorem nAdd_res {S lg x y p : ℕ} (hlg : n ≤ 2 ^ lg) (hx : x < 2 ^ (n * S)) (hy : y < 2 ^ (n * S))
    (hp : p < S) : resPN n S (addN S n lg x y) p = resPN n S x p + resPN n S y p := by
  obtain ⟨-, C, h1, h2, -⟩ := pf_addN hlg hx hy hp
  rw [resPN_vv, resPN_vv, resPN_vv]
  exact vv_add h1 h2

theorem nAdd_zero {S lg x y p : ℕ} (hlg : n ≤ 2 ^ lg) (hx : x < 2 ^ (n * S)) (hy : y < 2 ^ (n * S))
    (hp : p < S) (hzx : Zero n S x p) (hzy : Zero n S y p) : Zero n S (addN S n lg x y) p := by
  rw [zero_iff] at hzx hzy ⊢
  obtain ⟨-, C, h1, -, h3⟩ := pf_addN hlg hx hy hp
  intro k
  rw [h1, hzx k, hzy k, h3 hzx hzy k]
  rfl

theorem dvN_lt (j : ℕ) : dvN n j < n := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))

theorem nHalf_res {S j x p : ℕ} (hx : x < 2 ^ (n * S)) (hp : p < S) :
    resPN n S (rotN S n (dvN n j) x) p = hN n ^ j * resPN n S x p := by
  rw [res_rotN (dvN_lt j).le hx hp, hN, ← pow_mul]
  change (2 : ZMod (2 ^ n - 1)) ^ ((n - 1) * j % n) * _ = _
  rw [two_pow_mod]

theorem nRot_zero {S k x p : ℕ} (hk : k ≤ n) (hx : x < 2 ^ (n * S)) (hp : p < S)
    (hz : Zero n S x p) : Zero n S (rotN S n k x) p := fun b hb => by
  rw [testBit_rotN hk hx hb hp]
  exact hz _ (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n)))

theorem netN_eq (S n k N x : ℕ) : netN S n k N x = CFSG.KC.KDense.netP S k n N x := rfl

theorem nNet_bit {S k N x b p : ℕ} (hS : S = 2 ^ k) (h : CFSG.KC.KDense.netOK k N = true)
    (hb : b < n) (hp : p < S) :
    (netN S n k N x).testBit (b * S + p) = x.testBit (b * S + Benes.benesPerm k N p) := by
  rw [netN_eq, Nat.mul_comm b S, (Benes.testBit_netP hS h x).1 b hb p hp]

theorem nNet_bd {S k N x : ℕ} (hS : S = 2 ^ k) (h : CFSG.KC.KDense.netOK k N = true)
    (hx : x < 2 ^ (n * S)) : netN S n k N x < 2 ^ (n * S) :=
  bd_of_testBit fun i hi => by
    rw [netN_eq, (Benes.testBit_netP hS h x).2 i (by rw [Nat.mul_comm]; exact hi)]
    exact tb_hi hx hi

end LawAux

namespace LawAux

theorem xor_aux {a l b : ℕ} (ha : a % 2 = 0) (hl : l < 2 ^ b) :
    (2 ^ b * a + l) ^^^ 2 ^ b = 2 ^ b * (a + 1) + l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_two_pow_mul_add _ hl,
    Nat.testBit_two_pow]
  split_ifs with hj
  · rw [decide_eq_false (by omega), Bool.xor_false]
  · rcases hm : j - b with _ | m
    · rw [decide_eq_true (by omega), Nat.testBit_zero, Nat.testBit_zero]
      have : (a + 1) % 2 = 1 := by omega
      rw [this, ha]
      rfl
    · rw [decide_eq_false (by omega), Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ]
      congr 1
      omega

theorem xor_clear {p b : ℕ} (h : p.testBit b = false) : p ^^^ 2 ^ b = p + 2 ^ b := by
  have hl : p % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have e : p = 2 ^ b * (p / 2 ^ b) + p % 2 ^ b := (Nat.div_add_mod p (2 ^ b)).symm
  have ha : (p / 2 ^ b) % 2 = 0 := by
    have := Nat.testBit_mul_two_pow_add_eq (p / 2 ^ b) (p % 2 ^ b) b
    rw [← e, h, Nat.testBit_lt_two_pow hl] at this
    simp only [Bool.bne_false] at this
    by_contra hc
    rw [decide_eq_true (by omega)] at this
    exact absurd this (by decide)
  rw [e, xor_aux ha hl]
  ring

theorem bit_sub {p b : ℕ} (h : 2 ^ b ≤ p) : p.testBit b = !((p - 2 ^ b).testBit b) := by
  have := Nat.testBit_two_pow_add_eq (p - 2 ^ b) b
  rwa [Nat.add_sub_cancel' h] at this

theorem xor_set {p b : ℕ} (h : p.testBit b = true) : p ^^^ 2 ^ b = p - 2 ^ b := by
  have hle : 2 ^ b ≤ p := Nat.ge_two_pow_of_testBit h
  have hc : (p - 2 ^ b).testBit b = false := by
    have := bit_sub hle
    rw [h] at this
    cases hq : (p - 2 ^ b).testBit b
    · rfl
    · rw [hq] at this
      exact absurd this (by decide)
  have e := xor_clear hc
  rw [Nat.sub_add_cancel hle] at e
  calc p ^^^ 2 ^ b = ((p - 2 ^ b) ^^^ 2 ^ b) ^^^ 2 ^ b := by rw [e]
    _ = p - 2 ^ b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem hi_bit {k b q : ℕ} (hb : b < k) (hq : q < 2 ^ k) (h : 2 ^ k - 2 ^ b ≤ q) :
    q.testBit b = true := by
  cases hc : q.testBit b
  · have := (Benes.add_two_pow_of_clear hb hq hc).1
    omega
  · rfl

theorem testBit_clrN {k b p : ℕ} (hb : b < k) :
    (clrN (2 ^ k) b).testBit p = (decide (p < 2 ^ k) && !p.testBit b) := by
  rw [clrN, nxor, Nat.testBit_xor, ones_eq, Nat.testBit_two_pow_sub_one, Benes.idPlane_testBit hb]
  cases decide (p < 2 ^ k) <;> cases p.testBit b <;> rfl

theorem clrN_lt {k b : ℕ} (hb : b < k) : clrN (2 ^ k) b < 2 ^ 2 ^ k :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_clrN hb, decide_eq_false (by omega), Bool.false_and]

theorem xor_lt {k b p : ℕ} (hb : b < k) (hp : p < 2 ^ k) : p ^^^ 2 ^ b < 2 ^ k :=
  Nat.xor_lt_two_pow hp (Nat.pow_lt_pow_right (by decide) hb)

variable {n : ℕ}

theorem nXsw_bit {k b x b' p : ℕ} (hb : b < k) (hx : x < 2 ^ (n * 2 ^ k)) (hb' : b' < n)
    (hp : p < 2 ^ k) :
    (xswN (2 ^ k) n b x).testBit (b' * 2 ^ k + p) = x.testBit (b' * 2 ^ k + (p ^^^ 2 ^ b)) := by
  have hlo : ∀ c < n, ∀ q < 2 ^ k,
      (repN (2 ^ k) n (clrN (2 ^ k) b)).testBit (c * 2 ^ k + q) = !q.testBit b := by
    intro c hc q hq
    rw [testBit_repN (clrN_lt hb) hc hq, testBit_clrN hb, decide_eq_true hq, Bool.true_and]
  have hz : Bd n (2 ^ k) (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))) :=
    lt_of_le_of_lt Nat.and_le_left hx
  have hs : ∀ c < n, ∀ q < 2 ^ k, 2 ^ k - 2 ^ b ≤ q →
      (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))).testBit (c * 2 ^ k + q) = false := by
    intro c hc q hq hq'
    rw [nland, Nat.testBit_and, hlo c hc q hq, hi_bit hb hq hq', Bool.not_true, Bool.and_false]
  change (Nat.lor (Nat.land (Nat.shiftRight x (Nat.shiftLeft 1 b)) (repN (2 ^ k) n (clrN (2 ^ k) b)))
    (Nat.shiftLeft (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))) (Nat.shiftLeft 1 b))).testBit _ = _
  rw [nshl, Nat.one_shiftLeft, nlor, Nat.testBit_or, nshl, testBit_shl_pl hz hs hb' hp, nland,
    Nat.testBit_and, nshr, Nat.testBit_shiftRight, hlo b' hb' p hp]
  cases hpb : p.testBit b
  · have h2 : (if 2 ^ b ≤ p then (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))).testBit
        (b' * 2 ^ k + (p - 2 ^ b)) else false) = false := by
      split_ifs with h
      · rw [nland, Nat.testBit_and, hlo b' hb' _ (lt_of_le_of_lt (Nat.sub_le p _) hp)]
        have := bit_sub h
        rw [hpb] at this
        cases hq : (p - 2 ^ b).testBit b
        · rw [hq] at this
          exact absurd this (by decide)
        · rw [Bool.not_true, Bool.and_false]
      · rfl
    rw [h2, Bool.or_false, Bool.not_false, Bool.and_true, xor_clear hpb]
    congr 1
    omega
  · have h : 2 ^ b ≤ p := Nat.ge_two_pow_of_testBit hpb
    rw [Bool.not_true, Bool.and_false, Bool.false_or, if_pos h, nland, Nat.testBit_and,
      hlo b' hb' _ (lt_of_le_of_lt (Nat.sub_le p _) hp), xor_set hpb]
    have := bit_sub h
    rw [hpb] at this
    cases hq : (p - 2 ^ b).testBit b
    · rw [Bool.not_false, Bool.and_true]
    · rw [hq] at this
      exact absurd this (by decide)

theorem nXsw_bd {k b x : ℕ} (hb : b < k) (hx : x < 2 ^ (n * 2 ^ k)) :
    xswN (2 ^ k) n b x < 2 ^ (n * 2 ^ k) := by
  have hlo : ∀ c < n, ∀ q < 2 ^ k,
      (repN (2 ^ k) n (clrN (2 ^ k) b)).testBit (c * 2 ^ k + q) = !q.testBit b := by
    intro c hc q hq
    rw [testBit_repN (clrN_lt hb) hc hq, testBit_clrN hb, decide_eq_true hq, Bool.true_and]
  have hz : Bd n (2 ^ k) (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))) :=
    lt_of_le_of_lt Nat.and_le_left hx
  have hs : ∀ c < n, ∀ q < 2 ^ k, 2 ^ k - 2 ^ b ≤ q →
      (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))).testBit (c * 2 ^ k + q) = false := by
    intro c hc q hq hq'
    rw [nland, Nat.testBit_and, hlo c hc q hq, hi_bit hb hq hq', Bool.not_true, Bool.and_false]
  change Nat.lor (Nat.land (Nat.shiftRight x (Nat.shiftLeft 1 b)) (repN (2 ^ k) n (clrN (2 ^ k) b)))
    (Nat.shiftLeft (Nat.land x (repN (2 ^ k) n (clrN (2 ^ k) b))) (Nat.shiftLeft 1 b)) < _
  have e1 : Nat.shiftLeft 1 b = 2 ^ b := Nat.one_shiftLeft b
  rw [e1]
  exact Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (repN_lt (clrN_lt hb))) (bd_shl hz hs)

theorem bflyN_eq (S n lg b R x : ℕ) : bflyN S n lg b R x =
    Nat.lor (Nat.land x (Nat.xor (mN S n) (repN S n R)))
      (Nat.lor (addN S n lg (Nat.land x (repN S n (Nat.land R (clrN S b))))
          (Nat.land (Nat.shiftRight x (2 ^ b)) (repN S n (Nat.land R (clrN S b)))))
        (Nat.shiftLeft (addN S n lg (Nat.land x (repN S n (Nat.land R (clrN S b))))
          (negMN S n (Nat.land R (clrN S b))
            (Nat.land (Nat.shiftRight x (2 ^ b)) (repN S n (Nat.land R (clrN S b)))))) (2 ^ b))) := by
  rw [bflyN, nshl, Nat.one_shiftLeft]

variable [NeZero n]

theorem nBfly {k lg b R x : ℕ} (hlg : n ≤ 2 ^ lg) (hb : b < k) (hR : R < 2 ^ 2 ^ k)
    (hx : x < 2 ^ (n * 2 ^ k)) :
    bflyN (2 ^ k) n lg b R x < 2 ^ (n * 2 ^ k) ∧
    ((∀ q < 2 ^ k, R.testBit q = true → q.testBit b = false → R.testBit (q + 2 ^ b) = true) →
      ∀ p < 2 ^ k, R.testBit p = false →
        ∀ c < n, (bflyN (2 ^ k) n lg b R x).testBit (c * 2 ^ k + p) = x.testBit (c * 2 ^ k + p)) ∧
    (∀ p < 2 ^ k, R.testBit p = true → p.testBit b = false →
      resPN n (2 ^ k) (bflyN (2 ^ k) n lg b R x) p =
        resPN n (2 ^ k) x p + resPN n (2 ^ k) x (p + 2 ^ b)) ∧
    (∀ p < 2 ^ k, R.testBit p = true → p.testBit b = true →
      resPN n (2 ^ k) (bflyN (2 ^ k) n lg b R x) p =
        if R.testBit (p - 2 ^ b) = true then
          resPN n (2 ^ k) x (p - 2 ^ b) - resPN n (2 ^ k) x p else 0) := by
  set S := 2 ^ k with hS
  set lo := Nat.land R (clrN S b) with hlo_def
  set L := Nat.land x (repN S n lo) with hL_def
  set U := Nat.land (Nat.shiftRight x (2 ^ b)) (repN S n lo) with hU_def
  set T2 := addN S n lg L U with hT2
  set T3 := addN S n lg L (negMN S n lo U) with hT3
  have hlt : lo < 2 ^ S := lt_of_le_of_lt Nat.and_le_left hR
  have hloq : ∀ q < S, lo.testBit q = (R.testBit q && !q.testBit b) := by
    intro q hq
    rw [hlo_def, nland, Nat.testBit_and, testBit_clrN hb, decide_eq_true hq, Bool.true_and]
  have hLb : ∀ c < n, ∀ q < S, L.testBit (c * S + q) = (x.testBit (c * S + q) && lo.testBit q) := by
    intro c hc q hq
    rw [hL_def, nland, Nat.testBit_and, testBit_repN hlt hc hq]
  have hUb : ∀ c < n, ∀ q < S,
      U.testBit (c * S + q) = (x.testBit (c * S + (q + 2 ^ b)) && lo.testBit q) := by
    intro c hc q hq
    rw [hU_def, nland, Nat.testBit_and, nshr, Nat.testBit_shiftRight, testBit_repN hlt hc hq]
    congr 2
    omega
  have bL : L < 2 ^ (n * S) := lt_of_le_of_lt Nat.and_le_left hx
  have bU : U < 2 ^ (n * S) := lt_of_le_of_lt Nat.and_le_right (repN_lt hlt)
  have bNU : negMN S n lo U < 2 ^ (n * S) := nNeg_bd hlt bU
  have bT2 : T2 < 2 ^ (n * S) := nAdd_bd bL bU
  have bT3 : T3 < 2 ^ (n * S) := nAdd_bd bL bNU
  have zT : ∀ q < S, lo.testBit q = false → Zero n S T2 q ∧ Zero n S T3 q := by
    intro q hq h0
    have zL : Zero n S L q := fun c hc => by rw [hLb c hc q hq, h0, Bool.and_false]
    have zU : Zero n S U q := fun c hc => by rw [hUb c hc q hq, h0, Bool.and_false]
    exact ⟨nAdd_zero hlg bL bU hq zL zU,
      nAdd_zero hlg bL bNU hq zL (nNeg_zero hlt hq h0 zU)⟩
  have hs : ∀ c < n, ∀ q < S, S - 2 ^ b ≤ q → T3.testBit (c * S + q) = false := by
    intro c hc q hq hq'
    exact (zT q hq (by rw [hloq q hq, hi_bit hb hq hq', Bool.not_true, Bool.and_false])).2 c hc
  have hbits : ∀ c < n, ∀ p < S, (bflyN S n lg b R x).testBit (c * S + p) =
      ((x.testBit (c * S + p) && !R.testBit p) || T2.testBit (c * S + p) ||
        (if 2 ^ b ≤ p then T3.testBit (c * S + (p - 2 ^ b)) else false)) := by
    intro c hc p hp
    rw [bflyN_eq, nlor, nlor, nland, nxor, nshl, Nat.testBit_or, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_xor, testBit_mN, decide_eq_true (idx_lt hc hp), testBit_repN hR hc hp,
      testBit_shl_pl bT3 hs hc hp, Bool.true_xor]
    exact (Bool.or_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bflyN_eq]
    exact Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left hx)
      (Nat.or_lt_two_pow bT2 (bd_shl bT3 hs))
  · intro hc p hp hRp c hcn
    have hl0 : lo.testBit p = false := by rw [hloq p hp, hRp, Bool.false_and]
    rw [hbits c hcn p hp, hRp, Bool.not_false, Bool.and_true, (zT p hp hl0).1 c hcn, Bool.or_false]
    split_ifs with h
    · have hq : p - 2 ^ b < S := lt_of_le_of_lt (Nat.sub_le p _) hp
      have hl1 : lo.testBit (p - 2 ^ b) = false := by
        rw [hloq _ hq]
        cases hr : R.testBit (p - 2 ^ b)
        · rfl
        · cases hbq : (p - 2 ^ b).testBit b
          · have := hc _ hq hr hbq
            rw [Nat.sub_add_cancel h, hRp] at this
            exact absurd this (by decide)
          · rfl
      rw [(zT _ hq hl1).2 c hcn, Bool.or_false]
    · rw [Bool.or_false]
  · intro p hp hRp hpb
    have hl1 : lo.testBit p = true := by rw [hloq p hp, hRp, hpb]; rfl
    have hpd : p + 2 ^ b < S := (Benes.add_two_pow_of_clear hb hp hpb).1
    have e : resPN n S (bflyN S n lg b R x) p = resPN n S T2 p := by
      refine resPN_congr fun c hc => ?_
      rw [hbits c hc p hp, hRp, Bool.not_true, Bool.and_false, Bool.false_or]
      split_ifs with h
      · have hq : p - 2 ^ b < S := lt_of_le_of_lt (Nat.sub_le p _) hp
        have := bit_sub h
        rw [hpb] at this
        have hq1 : (p - 2 ^ b).testBit b = true := by
          cases hq2 : (p - 2 ^ b).testBit b
          · rw [hq2] at this
            exact absurd this (by decide)
          · rfl
        have hl0 : lo.testBit (p - 2 ^ b) = false := by rw [hloq _ hq, hq1, Bool.not_true, Bool.and_false]
        rw [(zT _ hq hl0).2 c hc, Bool.or_false]
      · rw [Bool.or_false]
    rw [e, hT2, nAdd_res hlg bL bU hp]
    congr 1
    · exact resPN_congr fun c hc => by rw [hLb c hc p hp, hl1, Bool.and_true]
    · exact res_move fun c hc => by rw [hUb c hc p hp, hl1, Bool.and_true]
  · intro p hp hRp hpb
    have h : 2 ^ b ≤ p := Nat.ge_two_pow_of_testBit hpb
    have hl0 : lo.testBit p = false := by rw [hloq p hp, hpb, Bool.not_true, Bool.and_false]
    have hq : p - 2 ^ b < S := lt_of_le_of_lt (Nat.sub_le p _) hp
    have hq1 : (p - 2 ^ b).testBit b = false := by
      have := bit_sub h
      rw [hpb] at this
      cases hq2 : (p - 2 ^ b).testBit b
      · rfl
      · rw [hq2] at this
        exact absurd this (by decide)
    have e : resPN n S (bflyN S n lg b R x) p = resPN n S T3 (p - 2 ^ b) := by
      refine res_move fun c hc => ?_
      rw [hbits c hc p hp, hRp, Bool.not_true, Bool.and_false, Bool.false_or, (zT p hp hl0).1 c hc,
        Bool.false_or, if_pos h]
    rw [e]
    cases hr : R.testBit (p - 2 ^ b)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact res_of_zero (zT _ hq (by rw [hloq _ hq, hr, Bool.false_and])).2
    · simp only [↓reduceIte]
      have hl1 : lo.testBit (p - 2 ^ b) = true := by rw [hloq _ hq, hr, hq1]; rfl
      rw [hT3, nAdd_res hlg bL bNU hq, nNeg_res hlt hq, hl1]
      simp only [↓reduceIte]
      rw [sub_eq_add_neg]
      congr 1
      · exact resPN_congr fun c hc => by rw [hLb c hc _ hq, hl1, Bool.and_true]
      · congr 1
        refine res_move fun c hc => ?_
        rw [hUb c hc _ hq, hl1, Bool.and_true, Nat.sub_add_cancel h]

end LawAux

namespace LawAux

theorem SA_pos : 0 < SA := by decide

theorem testBit_compactN (o Z : ℕ) : ∀ c i, (compactN c o Z).testBit i =
    (decide (i < c * SA) && Z.testBit (o + i / SA * SX + i % SA))
  | 0, i => by simp [compactN]
  | c + 1, i => by
    change (Nat.lor (compactN c o Z) (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.add o (Nat.mul c SX))) (ones SA)) (Nat.mul c SA))).testBit i = _
    rw [nlor, Nat.testBit_or, testBit_compactN o Z c i, nshl, nland, nshr, nadd, nmul, nmul,
      Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, ones_eq,
      Nat.testBit_two_pow_sub_one]
    have hS := SA_pos
    have e := Nat.div_add_mod' i SA
    rw [Nat.succ_mul]
    by_cases h1 : i < c * SA
    · have a1 : ¬ c * SA ≤ i := by omega
      have a2 : i < c * SA + SA := by omega
      simp [h1, a1, a2]
    · by_cases h2 : i < c * SA + SA
      · have hd : i / SA = c := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
        rw [hd] at e
        have a1 : c * SA ≤ i := by omega
        have a2 : i - c * SA < SA := by omega
        simp only [h1, h2, a1, a2, hd, decide_true, decide_false, Bool.false_and, Bool.false_or,
          Bool.true_and, Bool.and_true, ge_iff_le]
        congr 1
        omega
      · have a2 : ¬ i - c * SA < SA := by omega
        simp [h1, h2, a2]

theorem compactN_lt (n o Z : ℕ) : compactN n o Z < 2 ^ (n * SA) :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_compactN, decide_eq_false (by omega), Bool.false_and]

theorem compactN_bit {n o Z b p : ℕ} (hb : b < n) (hp : p < SA) :
    (compactN n o Z).testBit (b * SA + p) = Z.testBit (b * SX + (o + p)) := by
  rw [testBit_compactN, decide_eq_true (idx_lt hb hp), Bool.true_and, idx_mod hp,
    Nat.div_eq_of_lt_le (k := b) (by omega) (by rw [Nat.succ_mul]; omega)]
  have e : o + b * SX + p = b * SX + (o + p) := by omega
  rw [e]

theorem testBit_expandN {o Z : ℕ} (ho : o + SA ≤ SX) : ∀ c b p, p < SX →
    (expandN c o Z).testBit (b * SX + p) =
      (decide (b < c) && (decide (o ≤ p ∧ p < o + SA) && Z.testBit (b * SA + (p - o))))
  | 0, b, p, _ => by simp [expandN]
  | c + 1, b, p, hp => by
    change (Nat.lor (expandN c o Z) (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.mul c SA)) (ones SA)) (Nat.add o (Nat.mul c SX)))).testBit _ = _
    rw [nlor, Nat.testBit_or, testBit_expandN ho c b p hp, nshl, nland, nshr, nadd, nmul, nmul,
      Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, ones_eq,
      Nat.testBit_two_pow_sub_one]
    rcases Nat.lt_trichotomy b c with h | rfl | h
    · have := Nat.mul_le_mul_right SX (by omega : b + 1 ≤ c)
      rw [Nat.succ_mul] at this
      have a1 : ¬ o + c * SX ≤ b * SX + p := by omega
      have a2 : b < c + 1 := by omega
      simp [h, a1, a2]
    · have a0 : ¬ b < b := lt_irrefl b
      have a1 : b < b + 1 := by omega
      by_cases h1 : o ≤ p
      · by_cases h2 : p < o + SA
        · have a2 : o + b * SX ≤ b * SX + p := by omega
          have a3 : b * SX + p - (o + b * SX) < SA := by omega
          simp only [a0, a1, a2, a3, h1, h2, and_self, decide_true, decide_false, Bool.false_and,
            Bool.false_or, Bool.true_and, Bool.and_true, ge_iff_le]
          congr 1
          omega
        · have a3 : ¬ b * SX + p - (o + b * SX) < SA := by omega
          simp [a0, a1, a3, h2]
      · have a2 : ¬ o + b * SX ≤ b * SX + p := by omega
        simp [a0, a1, a2, h1]
    · have := Nat.mul_le_mul_right SX (by omega : c + 1 ≤ b)
      rw [Nat.succ_mul] at this
      have a0 : ¬ b < c := by omega
      have a1 : ¬ b < c + 1 := by omega
      have a3 : ¬ b * SX + p - (o + c * SX) < SA := by omega
      simp [a0, a1, a3]

theorem expandN_lt {o Z : ℕ} (ho : o + SA ≤ SX) : ∀ c, expandN c o Z < 2 ^ (c * SX)
  | 0 => by simp [expandN]
  | c + 1 => by
    change Nat.lor (expandN c o Z) (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.mul c SA)) (ones SA)) (Nat.add o (Nat.mul c SX))) < _
    rw [nlor, nshl, nland, nadd, nmul, ones_eq, Nat.shiftLeft_eq]
    refine Nat.or_lt_two_pow (Benes.lt_two_pow_mono (expandN_lt ho c) (by rw [Nat.succ_mul]; omega)) ?_
    have h1 := Benes.land_ones_lt (Nat.shiftRight Z (Nat.mul c SA)) SA
    calc _ < 2 ^ SA * 2 ^ (o + c * SX) := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ (SA + (o + c * SX)) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ ((c + 1) * SX) := Nat.pow_le_pow_right (by decide) (by rw [Nat.succ_mul]; omega)

end LawAux

theorem opsN_law {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) : PLaw n (opsN n lg) := by
  have : NeZero n := ⟨by omega⟩
  exact {
    rep_lt := fun hm => repN_lt hm
    rep_testBit := fun hm hb hp => testBit_repN hm hb hp
    neg_bd := fun hm hx => nNeg_bd hm hx
    neg_res := fun hm _ hp => nNeg_res hm hp
    add_bd := fun hx hy => nAdd_bd hx hy
    add_res := fun hx hy hp => nAdd_res hlg hx hy hp
    half_bd := fun _ _ _ => rotN_lt _ _ _ _
    half_res := fun _ _ hx hp => nHalf_res hx hp
    bfly_bd := by
      intro k S b R x hS hb hR hx
      subst hS
      exact (nBfly hlg hb hR hx).1
    bfly_res := by
      intro k S b R x p hS hb hR hc hx hp
      subst hS
      have H := nBfly hlg hb hR hx
      by_cases h1 : R.testBit p = false
      · rw [if_pos h1]
        exact resPN_congr fun c hc' => H.2.1 hc p hp h1 c hc'
      · rw [if_neg h1]
        have h1' : R.testBit p = true := by simpa using h1
        by_cases h2 : p.testBit b = false
        · rw [if_pos h2]
          exact H.2.2.1 p hp h1' h2
        · rw [if_neg h2]
          exact H.2.2.2 p hp h1' (by simpa using h2)
    net_bd := fun hS h hx => nNet_bd hS h hx
    net_res := fun hS h _ hp => res_move fun b hb => nNet_bit hS h hb hp
    xsw_bd := by
      intro k S b x hS hb hx
      subst hS
      exact nXsw_bd hb hx
    xsw_res := by
      intro k S b x p hS hb hx hp
      subst hS
      exact res_move fun c hc => nXsw_bit hb hx hc hp
    compact_bd := compactN_lt _ _ _
    compact_res := fun _ _ hp => res_move fun b hb => compactN_bit hb hp
    expand_bd := fun ho _ => expandN_lt ho n
    expand_res := by
      intro o Z p ho _ hp
      split_ifs with h
      · exact res_move fun b hb => by
          erw [testBit_expandN ho n b p hp, decide_eq_true hb, decide_eq_true h, Bool.true_and,
            Bool.true_and]
      · exact res_of_zero fun b hb => by
          erw [testBit_expandN ho n b p hp, decide_eq_false h, Bool.false_and, Bool.and_false]
    neg_zero := fun hm _ hp h0 hz => nNeg_zero hm hp h0 hz
    add_zero := fun hx hy hp hzx hzy => nAdd_zero hlg hx hy hp hzx hzy
    half_zero := fun _ _ hx hp hz => nRot_zero (dvN_lt _).le hx hp hz
    bfly_zero := by
      intro k S b R x p hS hb hR hc hx hp hRp hz
      subst hS
      intro c hc'
      erw [(nBfly hlg hb hR hx).2.1 hc p hp hRp c hc']
      exact hz c hc'
    net_zero := fun hS h _ hp hz b hb => by
      erw [nNet_bit hS h hb hp]
      exact hz b hb
    xsw_zero := by
      intro k S b x p hS hb hx hp hz
      subst hS
      intro c hc
      erw [nXsw_bit hb hx hc hp]
      exact hz c hc
    compact_zero := fun _ _ hp hz b hb => by
      erw [compactN_bit hb hp]
      exact hz b hb
    expand_zero := by
      intro o Z p ho _ hp hz b hb
      erw [testBit_expandN ho n b p hp]
      by_cases h : o ≤ p ∧ p < o + SA
      · rw [decide_eq_true h, hz h b hb, Bool.and_false, Bool.and_false]
      · rw [decide_eq_false h, Bool.false_and, Bool.and_false] }

namespace LawAux

theorem rep4_repN (S m : ℕ) : rep4 S m = repN S 4 m := by
  change (m ||| m <<< S) ||| (m ||| m <<< S) <<< (S <<< 1) =
    (((0 ||| m <<< (0 * S)) ||| m <<< (1 * S)) ||| m <<< (2 * S)) ||| m <<< (3 * S)
  have e1 : S * 2 = 2 * S := by ring
  have e2 : S + 2 * S = 3 * S := by ring
  rw [Nat.shiftLeft_eq S 1, pow_one, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.zero_or,
    Nat.zero_mul, Nat.shiftLeft_zero, Nat.one_mul, e1, e2, ← Nat.or_assoc]

theorem m4_mN (S : ℕ) : m4 S = mN S 4 := by
  unfold m4 mN
  rw [ones_eq, ones_eq]
  congr 2
  change S <<< 2 = 4 * S
  rw [Nat.shiftLeft_eq]
  ring

theorem rotk_rotN (S k x : ℕ) : rotk S k x = rotN S 4 k x := by
  unfold rotk rotN
  rw [m4_mN]

theorem negM_negMN (S m x : ℕ) : negM S m x = negMN S 4 m x := by
  unfold negM negMN
  rw [rep4_repN]

theorem add15_addN (S x y : ℕ) : add15 S x y = addN S 4 2 x y := by
  rw [addN_eq, kLoop_succ, kLoop_succ]
  unfold add15
  simp only [rotk_rotN]
  rfl

theorem bfly_bflyN (S b R x : ℕ) : bfly S b R x = bflyN S 4 2 b R x := by
  unfold bfly bflyN
  simp only [add15_addN, negM_negMN, rep4_repN, m4_mN]
  rfl

theorem net4_netN (S k N x : ℕ) : net4 S k N x = netN S 4 k N x := by
  unfold net4 netN
  simp only [rep4_repN]

theorem xsw_xswN (S b x : ℕ) : xsw S b x = xswN S 4 b x := by
  unfold xsw xswN
  simp only [rep4_repN]
  rfl

theorem half15 {S j x : ℕ} (h1 : 1 ≤ j) (h3 : j ≤ 3) :
    rotk S (Nat.sub 4 j) x = rotN S 4 (dvN 4 j) x := by
  rw [rotk_rotN]
  interval_cases j <;> rfl

theorem plaw_congr {np : ℕ} {O O' : POps} (h : PLaw np O) (e1 : O'.rep = O.rep)
    (e2 : O'.neg = O.neg) (e3 : O'.add = O.add)
    (e4 : ∀ S j x, 1 ≤ j → j ≤ 3 → O'.half S j x = O.half S j x) (e5 : O'.bfly = O.bfly)
    (e6 : O'.net = O.net) (e7 : O'.xsw = O.xsw) (e8 : O'.compact = O.compact)
    (e9 : O'.expand = O.expand) : PLaw np O' := by
  obtain ⟨r, ng, ad, hf, bf, nt, xs, cp, ex⟩ := O
  obtain ⟨r', ng', ad', hf', bf', nt', xs', cp', ex'⟩ := O'
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9
  subst e1 e2 e3 e5 e6 e7 e8 e9
  exact { h with
    half_bd := fun {S j x} h1 h3 hx => by
      dsimp only
      rw [e4 S j x h1 h3]
      exact h.half_bd h1 h3 hx
    half_res := fun {S j x p} h1 h3 hx hp => by
      dsimp only
      rw [e4 S j x h1 h3]
      exact h.half_res h1 h3 hx hp
    half_zero := fun {S j x p} h1 h3 hx hp hz => by
      dsimp only
      rw [e4 S j x h1 h3]
      exact h.half_zero h1 h3 hx hp hz }

end LawAux

theorem ops15_law : PLaw 4 ops15 :=
  plaw_congr (opsN_law (n := 4) (lg := 2) (by decide) (by decide))
    (funext fun S => funext fun m => rep4_repN S m)
    (funext fun S => funext fun m => funext fun x => negM_negMN S m x)
    (funext fun S => funext fun x => funext fun y => add15_addN S x y)
    (fun _ _ _ h1 h3 => half15 h1 h3)
    (funext fun S => funext fun b => funext fun R => funext fun x => bfly_bflyN S b R x)
    (funext fun S => funext fun k => funext fun N => funext fun x => net4_netN S k N x)
    (funext fun S => funext fun b => funext fun x => xsw_xswN S b x) rfl rfl

theorem bfly_needs_closure :
    resPN 4 2 (bfly 2 0 1 1) 1 ≠ resPN 4 2 1 1 ∧ resPN 4 2 (bflyN 2 4 2 0 1 1) 1 ≠ resPN 4 2 1 1 ∧
      ¬ (∀ q < 2, (1 : ℕ).testBit q = true → q.testBit 0 = false → (1 : ℕ).testBit (q + 2 ^ 0) = true) := by
  decide +kernel

end CFSG.KC.KStep

end
