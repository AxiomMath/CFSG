module

public import Certificates.Data.Kernel.OmegaCY.Search
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.OmegaCY

theorem cy_xorD (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem cy_nIfD (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem cy_bAndD (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bt_eq (a i : Nat) : bt a i = a.testBit i := by
  have h : Nat.land (Nat.shiftRight a i) (nat_lit 1) = (a / 2 ^ i) % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  unfold bt
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h0 | h1
  · rw [h0]
    rfl
  · rw [h1]
    rfl

theorem bfT_eq (tab a b i j o : Nat) : bfT tab a b i j o =
    if (a.testBit i && b.testBit j) = true then Nat.land (Nat.shiftRight tab o) 7 else 0 := by
  simp only [bfT, cy_bAndD, cy_nIfD, bt_eq]

theorem bf_eq (tab a b : Nat) : bf tab a b =
    ((bfT tab a b 4 3 27 ^^^ bfT tab a b 5 3 39) ^^^ (bfT tab a b 6 3 54 ^^^ bfT tab a b 5 4 42)) ^^^
      (bfT tab a b 6 4 57 ^^^ bfT tab a b 6 5 60) := rfl

theorem bm2_eq (tab a b : Nat) : bm2 tab a b = a ^^^ b ^^^ bf tab a b := rfl

theorem bfT_xl (tab a a' b i j o : Nat) :
    bfT tab (a ^^^ a') b i j o = bfT tab a b i j o ^^^ bfT tab a' b i j o := by
  simp only [bfT_eq, Nat.testBit_xor]
  cases a.testBit i <;> cases a'.testBit i <;> cases b.testBit j <;> simp

theorem bfT_xr (tab a b b' i j o : Nat) :
    bfT tab a (b ^^^ b') i j o = bfT tab a b i j o ^^^ bfT tab a b' i j o := by
  simp only [bfT_eq, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit j <;> cases b'.testBit j <;> simp

theorem bf_xl (tab a a' b : Nat) : bf tab (a ^^^ a') b = bf tab a b ^^^ bf tab a' b := by
  simp only [bf_eq, bfT_xl]
  ac_rfl

theorem bf_xr (tab a b b' : Nat) : bf tab a (b ^^^ b') = bf tab a b ^^^ bf tab a b' := by
  simp only [bf_eq, bfT_xr]
  ac_rfl

theorem bfT_lt (tab a b i j o : Nat) : bfT tab a b i j o < 2 ^ 3 := by
  rw [bfT_eq]
  split
  · exact Nat.lt_succ_of_le Nat.and_le_right
  · decide

theorem bf_lt (tab a b : Nat) : bf tab a b < 2 ^ 3 := by
  rw [bf_eq]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (bfT_lt ..) (bfT_lt ..))
    (Nat.xor_lt_two_pow (bfT_lt ..) (bfT_lt ..))) (Nat.xor_lt_two_pow (bfT_lt ..) (bfT_lt ..))

theorem testBit_of_lt8 {x : Nat} (hx : x < 2 ^ 3) {i : Nat} (hi : 3 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem bf_lo (tab : Nat) {x : Nat} (hx : x < 2 ^ 3) (b : Nat) : bf tab x b = 0 := by
  simp [bf_eq, bfT_eq, testBit_of_lt8 hx (le_refl 3), testBit_of_lt8 hx (by norm_num : 3 ≤ 4),
    testBit_of_lt8 hx (by norm_num : 3 ≤ 5), testBit_of_lt8 hx (by norm_num : 3 ≤ 6)]

theorem bf_rpow (tab : Nat) {b m : Nat} (hb : b < 2 ^ (m + 1)) : bf tab b (2 ^ m) = 0 := by
  have key : ∀ i j, j < i → (b.testBit i && decide (m = j)) = false := by
    intro i j hij
    by_cases h : m = j
    · subst h
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hij))]
      rfl
    · simp [h]
  simp only [bf_eq, bfT_eq, Nat.testBit_two_pow, key 4 3 (by norm_num), key 5 3 (by norm_num),
    key 6 3 (by norm_num), key 5 4 (by norm_num), key 6 4 (by norm_num), key 6 5 (by norm_num)]
  simp

theorem bf_zr (tab a : Nat) : bf tab a 0 = 0 := by
  simp [bf_eq, bfT_eq]

theorem mod_succ_true {a m : Nat} (ha : a.testBit m = true) : a % 2 ^ (m + 1) = a % 2 ^ m ^^^ 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i m with h | rfl | h
  · have h1 : i < m + 1 := by omega
    have h2 : m ≠ i := by omega
    simp [h, h1, h2]
  · simp [ha]
  · have h1 : ¬ i < m + 1 := by omega
    have h2 : ¬ i < m := by omega
    have h3 : m ≠ i := by omega
    simp [h1, h2, h3]

theorem mod_succ_false {a m : Nat} (ha : a.testBit m = false) : a % 2 ^ (m + 1) = a % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow]
  rcases lt_trichotomy i m with h | rfl | h
  · have h1 : i < m + 1 := by omega
    simp [h, h1]
  · simp [ha]
  · have h1 : ¬ i < m + 1 := by omega
    have h2 : ¬ i < m := by omega
    simp [h1, h2]

theorem cy_xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at e
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

theorem bm2_lt (tab : Nat) {a b : Nat} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) : bm2 tab a b < 2 ^ 7 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb)
    (lt_of_lt_of_le (bf_lt ..) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))

theorem bm2_step (tab a : Nat) {b m : Nat} (hb : b < 2 ^ m) :
    bm2 tab (bm2 tab a b) (2 ^ m) = bm2 tab a (b ^^^ 2 ^ m) := by
  have h1 : bf tab b (2 ^ m) = 0 :=
    bf_rpow tab (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h2 : bf tab (bf tab a b) (2 ^ m) = 0 := bf_lo tab (bf_lt ..) _
  simp only [bm2_eq, bf_xl, bf_xr, h1, h2, Nat.xor_zero]
  ac_rfl

variable {M : Type*} [Group M]

def psiG (g : ℕ → M) (k : ℕ) : ℕ → M
  | 0 => 1
  | m + 1 => psiG g k m * (if k.testBit m = true then g m else 1)

structure CyRel (tab : ℕ) (g : ℕ → M) : Prop where
  sq : ∀ i < 7, g i * g i = 1
  cen : ∀ i < 3, ∀ k < 7, g i * g k = g k * g i
  comm : ∀ i < 7, ∀ j < i, g i * g j = g j * g i * psiG g (bf tab (2 ^ i) (2 ^ j)) 3

variable {g : ℕ → M} {tab : ℕ}

theorem psiG_zero (k : ℕ) : psiG g k 0 = 1 := by
  simp only [psiG]

theorem psiG_succ (k m : ℕ) :
    psiG g k (m + 1) = psiG g k m * (if k.testBit m = true then g m else 1) := by
  simp only [psiG]

theorem psiG_of_zero : ∀ m, psiG g 0 m = 1
  | 0 => rfl
  | m + 1 => by rw [psiG_succ, psiG_of_zero m, Nat.zero_testBit]; simp

theorem psiG_congr {x y : ℕ} : ∀ {m : ℕ}, (∀ i < m, x.testBit i = y.testBit i) →
    psiG g x m = psiG g y m
  | 0, _ => rfl
  | m + 1, h => by
    rw [psiG_succ, psiG_succ, psiG_congr (fun i hi => h i (by omega)), h m (by omega)]

theorem psiG_flip {a j : ℕ} : ∀ {m : ℕ}, m ≤ j → psiG g (a ^^^ 2 ^ j) m = psiG g a m := by
  intro m hm
  apply psiG_congr
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (by omega), Bool.xor_false]

theorem psiG_mod {b n : ℕ} : ∀ {m : ℕ}, m ≤ n → psiG g (b % 2 ^ n) m = psiG g b m := by
  intro m hm
  apply psiG_congr
  intro i hi
  rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega : i < n), Bool.true_and]

theorem gp_xor {x : M} (hx : x * x = 1) (a b : Bool) :
    (if (a ^^ b) = true then x else 1) = (if a = true then x else 1) * (if b = true then x else 1) := by
  cases a <;> cases b <;> simp [hx]

theorem psi_cen (hr : CyRel tab g) (z : ℕ) {k : ℕ} (hk : k < 7) :
    ∀ {m : ℕ}, m ≤ 3 → psiG g z m * g k = g k * psiG g z m
  | 0, _ => by simp [psiG_zero]
  | m + 1, hm => by
    rw [psiG_succ, mul_assoc]
    have e : (if z.testBit m = true then g m else 1) * g k =
        g k * (if z.testBit m = true then g m else 1) := by
      split
      · exact hr.cen m (by omega) k hk
      · simp
    rw [e, ← mul_assoc, psi_cen hr z hk (m := m) (by omega), mul_assoc]

theorem psi_cen_if (hr : CyRel tab g) (z : ℕ) {k : ℕ} (hk : k < 7) {m : ℕ} (hm : m ≤ 3) (c : Bool) :
    psiG g z m * (if c = true then g k else 1) = (if c = true then g k else 1) * psiG g z m := by
  split
  · exact psi_cen hr z hk hm
  · simp

theorem low_hom (hr : CyRel tab g) : ∀ {m : ℕ}, m ≤ 3 → ∀ x y : ℕ,
    psiG g (x ^^^ y) m = psiG g x m * psiG g y m
  | 0, _, _, _ => by simp [psiG_zero]
  | m + 1, hm, x, y => by
    rw [psiG_succ (x ^^^ y) m, psiG_succ x m, psiG_succ y m, low_hom hr (by omega) x y,
      Nat.testBit_xor, gp_xor (hr.sq m (by omega))]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, psi_cen_if hr y (k := m) (m := m) (by omega) (by omega), mul_assoc]

theorem psi_xor_lo (hr : CyRel tab g) {m : ℕ} (h3 : 3 ≤ m) (h7 : m ≤ 7) (x : ℕ) {e : ℕ}
    (he : e < 2 ^ 3) : psiG g (x ^^^ e) m = psiG g x m * psiG g e 3 := by
  induction m, h3 using Nat.le_induction with
  | base => exact low_hom hr le_rfl x e
  | succ m hm ih =>
    have hb : e.testBit m = false := testBit_of_lt8 he hm
    rw [psiG_succ (x ^^^ e) m, psiG_succ x m, ih (by omega), Nat.testBit_xor, hb, Bool.xor_false,
      mul_assoc, psi_cen_if hr e (k := m) (m := 3) (by omega) le_rfl, ← mul_assoc]

theorem gen_step (hr : CyRel tab g) {j : ℕ} (hj : j < 7) (a : ℕ) {m : ℕ} (hjm : j + 1 ≤ m)
    (hm : m ≤ 7) : psiG g a m * g j =
      psiG g (a ^^^ 2 ^ j) m * psiG g (bf tab (a % 2 ^ m) (2 ^ j)) 3 := by
  induction m, hjm using Nat.le_induction with
  | base =>
    rw [bf_rpow tab (Nat.mod_lt _ (by positivity)), psiG_of_zero, mul_one, psiG_succ, psiG_succ,
      psiG_flip le_rfl, Nat.testBit_xor, Nat.testBit_two_pow_self, mul_assoc]
    cases a.testBit j
    · simp
    · simp [hr.sq j hj]
  | succ m hjm ih =>
    have ih' := ih (by omega)
    have hne : (2 ^ j : ℕ).testBit m = false := Nat.testBit_two_pow_of_ne (by omega)
    rw [psiG_succ a m, psiG_succ (a ^^^ 2 ^ j) m, Nat.testBit_xor, hne, Bool.xor_false]
    cases ha : a.testBit m
    · simp only [Bool.false_eq_true, if_false, mul_one]
      rw [mod_succ_false ha, ih']
    · simp only [if_true]
      rw [mod_succ_true ha, bf_xl, low_hom hr le_rfl]
      have hc := hr.comm m (by omega) j (by omega)
      have hq := psi_cen hr (bf tab (a % 2 ^ m) (2 ^ j)) (k := m) (m := 3) (by omega) le_rfl
      calc psiG g a m * g m * g j
          = psiG g a m * g j * g m * psiG g (bf tab (2 ^ m) (2 ^ j)) 3 := by
            rw [mul_assoc (psiG g a m) (g m) (g j), hc]
            simp only [mul_assoc]
        _ = _ := by
            rw [ih']
            simp only [mul_assoc]
            rw [← mul_assoc (psiG g (bf tab (a % 2 ^ m) (2 ^ j)) 3) (g m), hq]
            simp only [mul_assoc]

theorem psi_gen (hr : CyRel tab g) {j : ℕ} (hj : j < 7) {a : ℕ} (ha : a < 2 ^ 7) :
    psiG g a 7 * g j = psiG g (bm2 tab a (2 ^ j)) 7 := by
  rw [gen_step hr hj a (by omega) le_rfl, Nat.mod_eq_of_lt ha, bm2_eq,
    psi_xor_lo hr (by norm_num) le_rfl _ (bf_lt ..)]

theorem psi_mul (hr : CyRel tab g) {a b : ℕ} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) :
    psiG g (bm2 tab a b) 7 = psiG g a 7 * psiG g b 7 := by
  suffices h : ∀ m ≤ 7, ∀ b < 2 ^ m, psiG g a 7 * psiG g b m = psiG g (bm2 tab a b) 7 from
    (h 7 le_rfl b hb).symm
  intro m
  induction m with
  | zero =>
    intro _ b hb
    have : b = 0 := by simpa using hb
    subst this
    rw [psiG_zero, mul_one, bm2_eq, bf_zr, Nat.xor_zero, Nat.xor_zero]
  | succ m ih =>
    intro hm b hb
    have hb' : b % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
    rw [psiG_succ b m, ← psiG_mod (b := b) (n := m) le_rfl, ← mul_assoc, ih (by omega) _ hb']
    have hbm : b = b % 2 ^ (m + 1) := (Nat.mod_eq_of_lt hb).symm
    cases hbit : b.testBit m
    · simp only [Bool.false_eq_true, if_false, mul_one]
      conv_rhs => rw [hbm, mod_succ_false hbit]
    · simp only [if_true]
      rw [psi_gen hr (by omega) (bm2_lt tab ha (lt_of_lt_of_le hb' (Nat.pow_le_pow_right
        (by norm_num) (by omega)))), bm2_step tab a hb']
      conv_rhs => rw [hbm, mod_succ_true hbit]

theorem psi_inj (hr : CyRel tab g) (hne : ∀ k, 0 < k → k < 2 ^ 7 → psiG g k 7 ≠ 1) {a b : ℕ}
    (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) (h : psiG g a 7 = psiG g b 7) : a = b := by
  have he : bf tab b b < 2 ^ 3 := bf_lt ..
  have he7 : bf tab b b < 2 ^ 7 :=
    lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hk : psiG g (bm2 tab a b ^^^ bf tab b b) 7 = 1 := by
    have h1 : psiG g (bf tab b b) 7 = psiG g (bf tab b b) 3 := by
      have := psi_xor_lo hr (by norm_num) le_rfl 0 he (g := g)
      rwa [Nat.zero_xor, psiG_of_zero, one_mul] at this
    rw [psi_xor_lo hr (by norm_num) le_rfl _ he, psi_mul hr ha hb, h, ← psi_mul hr hb hb, bm2_eq,
      Nat.xor_self, Nat.zero_xor, h1, ← low_hom hr le_rfl, Nat.xor_self, psiG_of_zero]
  have hk0 : bm2 tab a b ^^^ bf tab b b = 0 := by
    by_contra h0
    exact hne _ (Nat.pos_of_ne_zero h0) (Nat.xor_lt_two_pow (bm2_lt tab ha hb) he7) hk
  have h2 : a ^^^ b ^^^ bf tab a b = bf tab b b := cy_xor_eq_zero hk0
  have hd : a ^^^ b = bf tab (a ^^^ b) b := by
    rw [bf_xl, ← h2]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases (bf tab a b).testBit i <;> rfl
  have hd0 : a ^^^ b = 0 := by
    have hlt : a ^^^ b < 2 ^ 3 := hd ▸ bf_lt ..
    rw [hd, bf_lo tab hlt]
  exact cy_xor_eq_zero hd0

theorem psi_region [Finite M] (hr : CyRel tab g)
    (hne : ∀ k, 0 < k → k < 2 ^ 7 → psiG g k 7 ≠ 1) (R : ℕ → Prop) [DecidablePred R]
    (S : Subgroup M) (hR : ∀ k < 2 ^ 7, R k → psiG g k 7 ∈ S)
    (hcard : Nat.card S ≤ ((Finset.range (2 ^ 7)).filter R).card) {k : ℕ} (hk : k < 2 ^ 7) :
    psiG g k 7 ∈ S ↔ R k := by
  classical
  refine ⟨fun hS => ?_, hR k hk⟩
  by_contra hRk
  set F := (Finset.range (2 ^ 7)).filter R
  have hkF : k ∉ F := by simp [F, hRk]
  have hlt : ∀ x ∈ insert k F, x < 2 ^ 7 := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hk
    · exact Finset.mem_range.1 (Finset.mem_filter.1 hx).1
  have hinj : Set.InjOn (fun x => psiG g x 7) (insert k F : Finset ℕ) := fun x hx y hy e =>
    psi_inj hr hne (hlt x hx) (hlt y hy) e
  have hsub : (((insert k F).image fun x => psiG g x 7 : Finset M) : Set M) ⊆ (S : Set M) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hS
    · exact hR x (hlt x (Finset.mem_insert_of_mem hx)) (Finset.mem_filter.1 hx).2
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_insert_of_notMem hkF,
    ← Nat.card_coe_set_eq] at h1
  change F.card + 1 ≤ Nat.card S at h1
  omega

end CFSG.KC.OmegaCY

end
