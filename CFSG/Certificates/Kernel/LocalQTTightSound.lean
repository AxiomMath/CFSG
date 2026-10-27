module

public import Certificates.Data.Kernel.LocalQT.Tight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightFinInputs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.LQT.T

open CFSG.QuasithinUnique.Setup.X1.Tight CFSG.KC.LQT.P CFSG.KC.Ord

private theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by cases a <;> rfl

private theorem orB_eq (a b : Bool) : CFSG.KC.Ord.orB a b = (a || b) := by cases a <;> rfl

private theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem allN_iff {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [allN]
  | succ m ih =>
    change CFSG.KC.Ord.andB (f m) (allN m f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

private theorem anyN_iff {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [anyN]
  | succ m ih =>
    change CFSG.KC.Ord.orB (f m) (anyN m f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

private theorem allL_iff {l : List ℕ} {f : ℕ → Bool} : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    change CFSG.KC.Ord.andB (f a) (allL l f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

private theorem bitB_eq (n k : ℕ) : bitB n k = n.testBit k := by
  have e : bitB n k = decide (0 < n &&& 2 ^ k) := by
    rw [← Nat.one_shiftLeft]
    exact Bool.eq_iff_iff.2 (by simp [bitB, Nat.blt_eq])
  rw [e]
  cases h : n.testBit k
  · have : n &&& 2 ^ k = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases hi : k = i
      · subst hi
        exact Or.inl h
      · exact Or.inr hi
    simp [this]
  · have : n &&& 2 ^ k ≠ 0 := by
      intro h0
      have := Nat.testBit_and n (2 ^ k) k
      rw [h0, Nat.zero_testBit, h, Nat.testBit_two_pow] at this
      simp at this
    simp only [decide_eq_true_eq]
    omega

private theorem brec_eq (c : ℕ) (b : Bool) :
    Bool.rec (motive := fun _ => ℕ) 0 c b = if b then c else 0 := by cases b <;> rfl

private theorem col_eq (F k : ℕ) : col F k = F / 32 ^ k % 32 := by
  have e : col F k = (F >>> (5 * k)) &&& (2 ^ 5 - 1) := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem col_lt (F k : ℕ) : col F k < 32 := by
  rw [col_eq]
  exact Nat.mod_lt _ (by norm_num)

private theorem col_xor (F G k : ℕ) : col (xorK F G) k = col F k ^^^ col G k := by
  have e : ∀ X, col X k = (X >>> (5 * k)) &&& 31 := fun _ => rfl
  have ex : xorK F G = F ^^^ G := rfl
  rw [ex, e, e, e]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  generalize F.testBit (5 * k + i) = a
  generalize G.testBit (5 * k + i) = b
  generalize Nat.testBit 31 i = c
  cases a <;> cases b <;> cases c <;> rfl

private theorem app5K_eq (F n : ℕ) : app5K F n = app5 (col F) n := by
  have e : app5K F n = ((((0 ^^^ Bool.rec (motive := fun _ => ℕ) 0 (col F 0) (bitB n 0)) ^^^
      Bool.rec (motive := fun _ => ℕ) 0 (col F 1) (bitB n 1)) ^^^
      Bool.rec (motive := fun _ => ℕ) 0 (col F 2) (bitB n 2)) ^^^
      Bool.rec (motive := fun _ => ℕ) 0 (col F 3) (bitB n 3)) ^^^
      Bool.rec (motive := fun _ => ℕ) 0 (col F 4) (bitB n 4) := rfl
  rw [e]
  simp only [brec_eq, bitB_eq, Nat.zero_xor]
  rfl

private theorem ite_lt (b : Bool) {a : ℕ} (h : a < 32) : (if b then a else 0) < 32 := by
  cases b <;> simp [h]

private theorem app5_lt {f : ℕ → ℕ} (hf : ∀ j < 5, f j < 32) (n : ℕ) : app5 f n < 32 := by
  have x : ∀ {a b : ℕ}, a < 32 → b < 32 → a ^^^ b < 32 := fun ha hb =>
    Nat.xor_lt_two_pow (n := 5) ha hb
  unfold app5
  exact x (x (x (x (ite_lt _ (hf 0 (by omega))) (ite_lt _ (hf 1 (by omega))))
    (ite_lt _ (hf 2 (by omega)))) (ite_lt _ (hf 3 (by omega)))) (ite_lt _ (hf 4 (by omega)))

private theorem app5_congr {f g : ℕ → ℕ} (h : ∀ j < 5, f j = g j) (n : ℕ) :
    app5 f n = app5 g n := by
  unfold app5
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)]

private theorem app5K_lt (F n : ℕ) : app5K F n < 32 := by
  rw [app5K_eq]
  exact app5_lt (fun j _ => col_lt F j) n

private theorem pack5_eq (g : ℕ → ℕ) :
    pack5 g = g 0 + g 1 * 32 + g 2 * 1024 + g 3 * 32768 + g 4 * 1048576 := by
  have e : pack5 g = 0 + g 0 <<< (5 * 0) + g 1 <<< (5 * 1) + g 2 <<< (5 * 2) + g 3 <<< (5 * 3) +
      g 4 <<< (5 * 4) := rfl
  rw [e]
  simp only [Nat.shiftLeft_eq]
  norm_num

private theorem col_pack5 {g : ℕ → ℕ} (hg : ∀ j < 5, g j < 32) {k : ℕ} (hk : k < 5) :
    col (pack5 g) k = g k := by
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have h2 := hg 2 (by omega)
  have h3 := hg 3 (by omega)
  have h4 := hg 4 (by omega)
  rw [col_eq, pack5_eq]
  interval_cases k <;> norm_num <;> omega

private theorem imgCard_congr {f g : ℕ → ℕ} (h : ∀ j < 5, f j = g j) : imgCard f = imgCard g := by
  have e : app5 f = app5 g := funext (app5_congr h)
  simp only [imgCard, e]

private theorem col_shiftK : ∀ j < 5, col shiftK j = shiftC j := by decide +kernel

private theorem col_dbK : ∀ j < 5, col dbK j = dbC j := by decide +kernel

private theorem app5K_dbK (z : ℕ) : app5K dbK z = app5 dbC z := by
  rw [app5K_eq]
  exact app5_congr col_dbK z

private theorem rotK_eq (m n : ℕ) : rotK m n = rotn m n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change app5K shiftK (rotK m n) = app5 shiftC (rotn m n)
    rw [app5K_eq, ih]
    exact app5_congr col_shiftK _

private theorem rotn_lt {m n : ℕ} (hn : n < 32) : rotn m n < 32 := by
  cases m with
  | zero => exact hn
  | succ m => exact app5_lt (by decide) _

private theorem brec_lt {a b : ℕ} (ha : a < 32) (hb : b < 32) (c : Bool) :
    Bool.rec (motive := fun _ => ℕ) a b c < 32 := by cases c <;> assumption

private theorem col_th0K {x y : ℕ} (hx : x < 32) (hy : y < 32) {k : ℕ} (hk : k < 5) :
    col (th0K x y) k = th0C x y k := by
  unfold th0K
  rw [col_pack5 (fun j _ => brec_lt (brec_lt (brec_lt (brec_lt (app5K_lt _ _) (app5K_lt _ _) _)
    (app5K_lt _ _) _) hy _) hx _) hk]
  simp only [app5K_dbK]
  interval_cases k <;> rfl

private theorem col_thK {x y : ℕ} (hx : x < 32) (hy : y < 32) (i : ℕ) {k : ℕ} (hk : k < 5) :
    col (thK x y i) k = thC x y i k := by
  unfold thK
  rw [col_pack5 (fun j _ => by rw [rotK_eq]; exact rotn_lt (col_lt _ _)) hk]
  rw [rotK_eq, col_th0K hx hy]
  · rfl
  · exact Nat.mod_lt _ (by norm_num)

private theorem imgK_eq (F : ℕ) : imgK F = imgCard (col F) := by
  have hor : ∀ m i, (Nat.rec (motive := fun _ => ℕ) 0
      (fun n acc => Nat.lor acc (Nat.shiftLeft 1 (app5K F n))) m).testBit i =
      decide (∃ n < m, app5K F n = i) := by
    intro m i
    induction m with
    | zero => simp
    | succ m ih =>
      change ((Nat.rec (motive := fun _ => ℕ) 0
        (fun n acc => Nat.lor acc (Nat.shiftLeft 1 (app5K F n))) m) ||| 1 <<< app5K F m).testBit i = _
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨n, hn, h⟩ | h)
        · exact ⟨n, Nat.lt_succ_of_lt hn, h⟩
        · exact ⟨m, Nat.lt_succ_self m, h⟩
      · rintro ⟨n, hn, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
        · exact Or.inl ⟨n, hn, h⟩
        · exact Or.inr h
  have hcnt : ∀ s m, (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => ℕ) 0 1 (bitB s i))) m) =
      ((Finset.range m).filter (fun i => s.testBit i = true)).card := by
    intro s m
    induction m with
    | zero => simp
    | succ m ih =>
      change Nat.rec (motive := fun _ => ℕ) 0
        (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => ℕ) 0 1 (bitB s i))) m +
        Bool.rec (motive := fun _ => ℕ) 0 1 (bitB s m) = _
      rw [ih, Finset.range_add_one, Finset.filter_insert, bitB_eq]
      cases h : s.testBit m
      · simp
      · simp only [↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
  unfold imgK
  rw [strictN_eq, hcnt]
  unfold imgCard
  refine congrArg Finset.card ?_
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, hor, decide_eq_true_eq]
  simp only [app5K_eq]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨n, hn, h⟩
    exact ⟨h ▸ app5_lt (fun j _ => col_lt F j) n, n, hn, h⟩

private theorem goodK_iff {x y : ℕ} (hx : x < 32) (hy : y < 32) :
    goodK x y = true ↔ good x y = true := by
  have hth := fun i k (hk : k < 5) => col_thK hx hy i hk
  have hA : allN 5 (fun k => Nat.beq
      (Nat.xor (Nat.xor (Nat.xor (Nat.xor (col (thK x y 0) k) (col (thK x y 1) k))
        (col (thK x y 2) k)) (col (thK x y 3) k)) (col (thK x y 4) k)) (Nat.shiftLeft 1 k)) =
      true ↔ (List.range 5).all (fun k => (thC x y 0 k ^^^ thC x y 1 k ^^^ thC x y 2 k ^^^
        thC x y 3 k ^^^ thC x y 4 k) == 2 ^ k) = true := by
    rw [allN_iff, List.all_eq_true]
    simp only [List.mem_range, Nat.beq_eq, beq_iff_eq]
    refine forall_congr' fun k => imp_congr_right fun hk => ?_
    rw [hth 0 k hk, hth 1 k hk, hth 2 k hk, hth 3 k hk, hth 4 k hk, ← Nat.one_shiftLeft]
    rfl
  have hB : imgK (th0K x y) = imgCard (th0C x y) := by
    rw [imgK_eq]
    exact imgCard_congr fun j hj => col_th0K hx hy hj
  have hC : imgK (xorK (thK x y 0) (thK x y 1)) = imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k) := by
    rw [imgK_eq]
    refine imgCard_congr fun j hj => ?_
    rw [col_xor, hth 0 j hj, hth 1 j hj]
  have hD : imgK (xorK (xorK (xorK (thK x y 0) (thK x y 1)) (thK x y 2)) (thK x y 3)) =
      imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k ^^^ thC x y 2 k ^^^ thC x y 3 k) := by
    rw [imgK_eq]
    refine imgCard_congr fun j hj => ?_
    rw [col_xor, col_xor, col_xor, hth 0 j hj, hth 1 j hj, hth 2 j hj, hth 3 j hj]
  have hB' : Nat.beq (imgK (th0K x y)) 32 = (imgCard (th0C x y) == 32) := by
    rw [hB]
    exact Bool.eq_iff_iff.2 (by simp only [Nat.beq_eq, beq_iff_eq])
  have hC' : Nat.ble 16 (imgK (xorK (thK x y 0) (thK x y 1))) =
      decide (16 ≤ imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k)) := by
    rw [hC]
    exact Bool.eq_iff_iff.2 (by simp only [Nat.ble_eq, decide_eq_true_eq])
  have hD' : Nat.ble 16 (imgK (xorK (xorK (xorK (thK x y 0) (thK x y 1)) (thK x y 2)) (thK x y 3))) =
      decide (16 ≤ imgCard (fun k => thC x y 0 k ^^^ thC x y 1 k ^^^ thC x y 2 k ^^^ thC x y 3 k)) := by
    rw [hD]
    exact Bool.eq_iff_iff.2 (by simp only [Nat.ble_eq, decide_eq_true_eq])
  unfold goodK
  rw [Bool.eq_iff_iff.2 hA, hB', hC', hD', andB_eq, andB_eq, andB_eq]
  unfold good
  rw [Bool.and_assoc, Bool.and_assoc]

theorem s4038a {xs : List ℕ} {N : ℕ} (hx : ∀ x ∈ xs, x < 32) (hN : N ≤ 32)
    (h : c4038a xs N = true) : ∀ x ∈ xs, ∀ y < N, good x y = false := by
  intro x hxs y hy
  have h1 := allN_iff.1 (allL_iff.1 h x hxs) y hy
  have h2 : goodK x y = false := by
    cases e : goodK x y
    · rfl
    · rw [e] at h1
      exact absurd h1 (by decide)
  cases e : good x y
  · rfl
  · rw [(goodK_iff (hx x hxs) (by omega)).2 e] at h2
    exact absurd h2 (by decide)

theorem s4038b {N : ℕ} (hN : N ≤ 32) (h : c4038b N = true) :
    ∀ w < N,
      (∀ k < 5, app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (2 ^ k)))) = 2 ^ k) →
        ∃ x < 32, cycOK x = true ∧ app5 (dwC w) x = x := by
  intro w hw hord
  have hw32 : w < 32 := by omega
  have hD : ∀ z, app5K (dwK w) z = app5 (dwC w) z := by
    intro z
    rw [app5K_eq]
    refine app5_congr (fun j hj => ?_) z
    unfold dwK
    rw [col_pack5 (fun j _ => by rw [rotK_eq]; exact rotn_lt hw32) hj, rotK_eq]
    rfl
  have h1 := allN_iff.1 h w hw
  rw [letB_eq] at h1
  have hprem : allN 5 (fun k => Nat.beq (app5K (dwK w) (app5K (dwK w) (app5K (dwK w)
      (app5K (dwK w) (Nat.shiftLeft 1 k))))) (Nat.shiftLeft 1 k)) = true := by
    rw [allN_iff]
    intro k hk
    have e : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
    rw [e, hD, hD, hD, hD, hord k hk]
    exact Nat.beq_refl _
  rw [hprem] at h1
  have h2 : anyN 32 (fun x => CFSG.KC.Ord.andB (cycK x) (Nat.beq (app5K (dwK w) x) x)) = true := h1
  obtain ⟨x, hx, hxe⟩ := anyN_iff.1 h2
  change CFSG.KC.Ord.andB _ _ = true at hxe
  rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, hD] at hxe
  refine ⟨x, hx, ?_, hxe.2⟩
  have hc := hxe.1
  unfold cycK at hc
  rw [letB_eq, allN_iff] at hc
  have hF : ∀ e, app5K (pack5 fun k => rotK k x) e = app5 (fun k => rotn k x) e := by
    intro e
    rw [app5K_eq]
    refine app5_congr (fun j hj => ?_) e
    rw [col_pack5 (fun j _ => by rw [rotK_eq]; exact rotn_lt hx) hj, rotK_eq]
  unfold cycOK
  rw [List.all_eq_true]
  intro z hz
  rw [List.mem_range] at hz
  obtain ⟨e, he, hee⟩ := anyN_iff.1 (hc z hz)
  rw [List.any_eq_true]
  refine ⟨e, List.mem_range.2 he, ?_⟩
  rw [Nat.beq_eq, hF] at hee
  exact beq_iff_eq.2 hee

end CFSG.KC.LQT.T

end
