module

public import Certificates.Data.Kernel.RouteCK

public section

namespace CFSG.Certificates.Kernel.RouteCK

open CFSG.CGT.PushingUpLit.CGT6.RouteC CFSG.CGT.PushingUpLit.CGT6.RouteCK

theorem forceN_eq {β : Sort _} (y : Nat) (k : Nat → β) : forceN y k = k y := by
  cases y <;> rfl

theorem appR_eq {α : Type} (l r : List α) : appR l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (x :: ·) ih

theorem mapR_eq {α β : Type} (f : α → β) (l : List α) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (f x :: ·) ih

theorem flatMapR_eq {α β : Type} (f : α → List β) (l : List α) : flatMapR f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change appR (f x) (flatMapR f l) = _
    rw [appR_eq, ih, List.flatMap_cons]

theorem allL_eq (p : Nat → Bool) (l : List Nat) : allL p l = l.all p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change (p x && allL p l) = _
    rw [ih, List.all_cons]

theorem anyL_eq (p : Nat → Bool) (l : List Nat) : anyL p l = l.any p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change (p x || anyL p l) = _
    rw [ih, List.any_cons]

theorem rangeR_eq {α : Type} (f : Nat → List α) (lo cnt : Nat) :
    rangeR f lo cnt = (List.range' lo cnt).flatMap f := by
  induction cnt generalizing lo with
  | zero => rfl
  | succ c ih =>
    change forceN lo (fun lo => appR (f lo) (rangeR f (Nat.succ lo) c)) = _
    rw [forceN_eq, appR_eq, ih, List.range'_succ, List.flatMap_cons]

theorem filterR_eq (p : Nat → Bool) (lo cnt : Nat) :
    filterR p lo cnt = (List.range' lo cnt).filter p := by
  unfold filterR
  rw [rangeR_eq]
  induction List.range' lo cnt with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, ih, List.filter_cons]
    cases p x <;> rfl

def Sm (A : List Nat) : Prop := A.length ≤ 6 ∧ ∀ x ∈ A, x < 64

theorem packL_cons (a : Nat) (A : List Nat) : packL (a :: A) = a + 64 * packL A := rfl

theorem packL_nil : packL [] = 0 := rfl

theorem mvR_zero' (P v : Nat) : mvR 0 P v = 0 := rfl

theorem mvR_succ (k P v : Nat) : mvR (k + 1) P v = P % 64 * (v % 2) ^^^ mvR k (P / 64) (v / 2) :=
  rfl

theorem mulR_zero' (P B : Nat) : mulR P 0 B = 0 := rfl

theorem mulR_succ (P k B : Nat) : mulR P (k + 1) B = mv P (B % 64) + 64 * mulR P k (B / 64) := rfl

theorem mvR_zero (k v : Nat) : mvR k 0 v = 0 := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [mvR_succ, ih]; simp

theorem mul_bit (a v : Nat) : a * (v % 2) = if v % 2 = 1 then a else 0 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem mvR_packL (A : List Nat) (hA : ∀ x ∈ A, x < 64) (k : Nat) (hk : A.length ≤ k) (v : Nat) :
    mvR k (packL A) v = mulVec A v := by
  induction A generalizing k v with
  | nil => rw [packL_nil, mvR_zero]; rfl
  | cons a A ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have ha : a < 64 := hA a (by simp)
    rw [mvR_succ]
    have h1 : packL (a :: A) % 64 = a := by
      rw [packL_cons]
      omega
    have h2 : packL (a :: A) / 64 = packL A := by
      rw [packL_cons]
      omega
    rw [h1, h2, ih (fun x hx => hA x (by simp [hx])) k (by simp at hk; omega)]
    change a * (v % 2) ^^^ mulVec A (v / 2) = _
    rw [mul_bit]
    rfl

theorem mv_eq (P v : Nat) : mv P v = mvR 6 P v := by
  simp only [mvR_succ, mvR_zero', Nat.div_div_eq_div_mul, Nat.xor_zero]
  rfl

theorem mv_packL (A : List Nat) (hA : Sm A) (v : Nat) : mv (packL A) v = mulVec A v := by
  rw [mv_eq, mvR_packL A hA.2 6 hA.1]

theorem mulVec_lt (A : List Nat) (hA : ∀ x ∈ A, x < 64) (v : Nat) : mulVec A v < 64 := by
  induction A generalizing v with
  | nil => change 0 < 64; omega
  | cons a A ih =>
    change (if v % 2 = 1 then a else 0) ^^^ mulVec A (v / 2) < 64
    have h1 : (if v % 2 = 1 then a else 0) < 2 ^ 6 := by
      split
      · exact hA a (by simp)
      · decide
    exact Nat.xor_lt_two_pow h1 (ih (fun x hx => hA x (by simp [hx])) _)

theorem mv_zero (P : Nat) : mv P 0 = 0 := by
  rw [mv_eq]
  simp [mvR_succ, mvR_zero']

theorem mulR_packL (P : Nat) (B : List Nat) (hB : ∀ x ∈ B, x < 64) (k : Nat) (hk : B.length ≤ k) :
    mulR P k (packL B) = packL (B.map (mv P)) := by
  induction B generalizing k with
  | nil =>
    rw [packL_nil]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [mulR_succ, Nat.zero_mod, Nat.zero_div, ih (by simp), mv_zero]
      rfl
  | cons b B ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hb : b < 64 := hB b (by simp)
    rw [mulR_succ]
    have h1 : packL (b :: B) % 64 = b := by
      rw [packL_cons]
      omega
    have h2 : packL (b :: B) / 64 = packL B := by
      rw [packL_cons]
      omega
    rw [h1, h2, ih (fun x hx => hB x (by simp [hx])) k (by simp at hk; omega)]
    rfl

theorem mulK_eq (A B : Nat) : mulK A B = mulR A 6 B := by
  simp only [mulR_succ, mulR_zero', Nat.div_div_eq_div_mul, Nat.mul_zero, Nat.add_zero]
  simp only [mulK, forceN_eq]
  change mv A (B % 64) + (64 * mv A (B / 64 % 64) + (4096 * mv A (B / 4096 % 64) +
    (262144 * mv A (B / 262144 % 64) + (16777216 * mv A (B / 16777216 % 64) +
    1073741824 * mv A (B / 1073741824 % 64))))) = _
  simp only [Nat.reduceMul]
  omega

theorem Sm_mul {A B : List Nat} (hA : Sm A) (hB : Sm B) : Sm (mul A B) := by
  refine ⟨by simp [mul]; exact hB.1, ?_⟩
  intro x hx
  simp only [mul, List.mem_map] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact mulVec_lt A hA.2 v

theorem mulK_packL {A B : List Nat} (hA : Sm A) (hB : Sm B) :
    mulK (packL A) (packL B) = packL (mul A B) := by
  rw [mulK_eq, mulR_packL _ B hB.2 6 hB.1]
  unfold mul
  congr 1
  exact List.map_congr_left (fun v _ => mv_packL A hA v)

theorem Sm_one : Sm one := ⟨by decide, by decide⟩

theorem oneK_eq : oneK = packL one := rfl

theorem powK_packL {A : List Nat} (hA : Sm A) (k : Nat) :
    powK (packL A) k = packL (pow A k) ∧ Sm (pow A k) := by
  unfold powK
  rw [forceN_eq]
  induction k with
  | zero => exact ⟨rfl, Sm_one⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    change mulK (packL A) (Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulK (packL A) acc) k)
      = _ ∧ _
    rw [h1, mulK_packL hA h2]
    exact ⟨rfl, Sm_mul hA h2⟩

theorem Sm_chartY (φ : Nat) : Sm (chartY φ) := by
  refine ⟨by simp [chartY], ?_⟩
  simp only [chartY, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem Sm_chartD (ψ : Nat) : Sm (chartD ψ) := by
  refine ⟨by simp [chartD], ?_⟩
  simp only [chartD, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem Sm_chartT : Sm chartT := ⟨by decide, by decide⟩

theorem Sm_gen (φ ψ l : Nat) : Sm (gen φ ψ l) := by
  match l with
  | 0 => exact Sm_chartY φ
  | 1 => exact Sm_chartD ψ
  | 2 => exact Sm_chartT
  | 3 => exact Sm_mul (Sm_chartY φ) (Sm_chartY φ)
  | k + 4 => exact Sm_mul (Sm_chartD ψ) (Sm_chartD ψ)

theorem packL_lt (A : List Nat) (hA : ∀ x ∈ A, x < 64) : packL A < 64 ^ A.length := by
  induction A with
  | nil => exact Nat.one_pos
  | cons a A ih =>
    have ha : a < 64 := hA a (by simp)
    have := ih (fun x hx => hA x (by simp [hx]))
    rw [packL_cons, List.length_cons, Nat.pow_succ]
    have : 64 * packL A + 64 ≤ 64 * 64 ^ A.length := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ this
    rw [Nat.mul_comm (64 ^ A.length)]
    omega

theorem packL_lt36 {A : List Nat} (hA : Sm A) : packL A < 68719476736 := by
  have h := packL_lt A hA.2
  have : 64 ^ A.length ≤ 64 ^ 6 := Nat.pow_le_pow_right (by omega) hA.1
  have e : (64 : Nat) ^ 6 = 68719476736 := rfl
  omega

theorem genK_eq (G l : Nat) : genK G l = G / 68719476736 ^ (min l 4) % 68719476736 := by
  unfold genK
  have : Nat.sub 4 (Nat.sub 4 l) = min l 4 := by
    change 4 - (4 - l) = _
    omega
  rw [this]
  rfl

theorem dig_mod {a c : Nat} (r : Nat) (h : a < c) : (a + c * r) % c = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem dig_div {a c : Nat} (r : Nat) (h : a < c) : (a + c * r) / c = r := by
  have hc : 0 < c := by omega
  rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt h, Nat.zero_add]

theorem genK_letters (φ ψ l : Nat) : genK (lettersK φ ψ) l = packL (gen φ ψ l) := by
  have hY := packL_lt36 (Sm_chartY φ)
  have hD := packL_lt36 (Sm_chartD ψ)
  have hT := packL_lt36 Sm_chartT
  have hYY := packL_lt36 (Sm_mul (Sm_chartY φ) (Sm_chartY φ))
  have hDD := packL_lt36 (Sm_mul (Sm_chartD ψ) (Sm_chartD ψ))
  have hL : lettersK φ ψ = packL (chartY φ) + 68719476736 * (packL (chartD ψ) + 68719476736 *
      (packL chartT + 68719476736 * (packL (mul (chartY φ) (chartY φ)) + 68719476736 *
      packL (mul (chartD ψ) (chartD ψ))))) := by
    unfold lettersK
    rw [forceN_eq, forceN_eq, mulK_packL (Sm_chartY φ) (Sm_chartY φ),
      mulK_packL (Sm_chartD ψ) (Sm_chartD ψ)]
    rfl
  rw [genK_eq, hL]
  have p1 : ∀ x : Nat, x / 68719476736 ^ 1 = x / 68719476736 := fun x => by rw [Nat.pow_one]
  have p2 : ∀ k x : Nat, x / 68719476736 ^ (k + 1) = x / 68719476736 ^ k / 68719476736 :=
    fun k x => by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  match l with
  | 0 => rw [Nat.min_eq_left (by omega), Nat.pow_zero, Nat.div_one, dig_mod _ hY]; rfl
  | 1 => rw [Nat.min_eq_left (by omega), p1, dig_div _ hY, dig_mod _ hD]; rfl
  | 2 =>
    rw [Nat.min_eq_left (by omega), p2, p1, dig_div _ hY, dig_div _ hD, dig_mod _ hT]; rfl
  | 3 =>
    rw [Nat.min_eq_left (by omega), p2, p2, p1, dig_div _ hY, dig_div _ hD, dig_div _ hT,
      dig_mod _ hYY]; rfl
  | k + 4 =>
    rw [Nat.min_eq_right (by omega), p2, p2, p2, p1, dig_div _ hY, dig_div _ hD, dig_div _ hT,
      dig_div _ hYY, Nat.mod_eq_of_lt hDD]; rfl

theorem evalWK_aux (φ ψ : Nat) (w : List Nat) : ∀ acc, Sm acc →
    List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun l _ ih acc => forceN (mulK acc (genK (lettersK φ ψ) l)) ih) w (packL acc) =
      packL (w.foldl (fun acc l => mul acc (gen φ ψ l)) acc) ∧
    Sm (w.foldl (fun acc l => mul acc (gen φ ψ l)) acc) := by
  induction w with
  | nil => exact fun acc h => ⟨rfl, h⟩
  | cons l w ih =>
    intro acc h
    change forceN (mulK (packL acc) (genK (lettersK φ ψ) l)) _ = _ ∧ _
    rw [forceN_eq, genK_letters, mulK_packL h (Sm_gen φ ψ l)]
    exact ih _ (Sm_mul h (Sm_gen φ ψ l))

theorem evalWK_eq (φ ψ : Nat) (w : List Nat) :
    evalWK (lettersK φ ψ) w = packL (evalW φ ψ w) ∧ Sm (evalW φ ψ w) :=
  evalWK_aux φ ψ w one Sm_one

theorem xorC_packL (k : Nat) (A B : List Nat) (hA : ∀ x ∈ A, x < 64) (hB : ∀ x ∈ B, x < 64)
    (hlA : A.length = k) (hlB : B.length = k) : xorC k (packL A) (packL B) = add A B := by
  induction k generalizing A B with
  | zero =>
    rw [List.length_eq_zero_iff] at hlA hlB
    subst hlA hlB
    rfl
  | succ k ih =>
    obtain ⟨a, A, rfl⟩ := List.exists_cons_of_length_eq_add_one hlA
    obtain ⟨b, B, rfl⟩ := List.exists_cons_of_length_eq_add_one hlB
    have ha : a < 64 := hA a (by simp)
    have hb : b < 64 := hB b (by simp)
    change (packL (a :: A) % 64 ^^^ packL (b :: B) % 64) ::
      xorC k (packL (a :: A) / 64) (packL (b :: B) / 64) = _
    rw [packL_cons, packL_cons, dig_mod _ ha, dig_mod _ hb, dig_div _ ha, dig_div _ hb,
      ih A B (fun x hx => hA x (by simp [hx])) (fun x hx => hB x (by simp [hx]))
        (by simpa using hlA) (by simpa using hlB)]
    rfl

theorem allC_packL (q : Nat → Bool) (k : Nat) (A B : List Nat) (hA : ∀ x ∈ A, x < 64)
    (hB : ∀ x ∈ B, x < 64) (hlA : A.length = k) (hlB : B.length = k) :
    allC (fun a b => q (Nat.xor a b)) k (packL A) (packL B) = (add A B).all q := by
  induction k generalizing A B with
  | zero =>
    rw [List.length_eq_zero_iff] at hlA hlB
    subst hlA hlB
    rfl
  | succ k ih =>
    obtain ⟨a, A, rfl⟩ := List.exists_cons_of_length_eq_add_one hlA
    obtain ⟨b, B, rfl⟩ := List.exists_cons_of_length_eq_add_one hlB
    have ha : a < 64 := hA a (by simp)
    have hb : b < 64 := hB b (by simp)
    change (q (packL (a :: A) % 64 ^^^ packL (b :: B) % 64) &&
      allC (fun a b => q (Nat.xor a b)) k (packL (a :: A) / 64) (packL (b :: B) / 64)) = _
    rw [packL_cons, packL_cons, dig_mod _ ha, dig_mod _ hb, dig_div _ ha, dig_div _ hb,
      ih A B (fun x hx => hA x (by simp [hx])) (fun x hx => hB x (by simp [hx]))
        (by simpa using hlA) (by simpa using hlB)]
    rfl

theorem memK_eq (M v : Nat) : memK M v = M.testBit v := by
  change Nat.beq (M / 2 ^ v % 2) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.beq_eq, decide_eq_true_eq]

theorem testBit_selK (m t c x : Nat) (hc : c ≤ 1) :
    (selK m t c).testBit x = if c = 0 then m.testBit x else t.testBit x := by
  unfold selK
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp
  · change (m ^^^ ((m ^^^ t) * 1)).testBit x = _
    rw [Nat.mul_one, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rfl

abbrev SwapKey (s M x : Nat) : Prop :=
  (M.testBit x = true ∧ s + x = x ^^^ s ∧ (s ≤ x → M.testBit (x - s) = false)) ∨
  (M.testBit x = false ∧ s ≤ x ∧ M.testBit (x - s) = true ∧ x - s = x ^^^ s)

theorem testBit_swapK (m s M x : Nat) (hk : SwapKey s M x) :
    (swapK m s M).testBit x = m.testBit (x ^^^ s) := by
  change ((m >>> s &&& M) ||| ((m &&& M) <<< s)).testBit x = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · rw [h1, h2]
    by_cases hs : s ≤ x
    · simp [h3 hs]
    · simp [hs]
  · rw [← h4]
    simp [h1, h2, h3]

theorem bitK_le (b j : Nat) : bitK b j ≤ 1 := by
  unfold bitK
  change b / 2 ^ j % 2 ≤ 1
  omega

theorem testBit_stage (m s M b j x : Nat) (hk : SwapKey s M x) :
    (selK m (swapK m s M) (bitK b j)).testBit x = m.testBit (x ^^^ bitK b j * s) := by
  rw [testBit_selK _ _ _ _ (bitK_le b j)]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (bitK_le b j) with h | h <;> rw [h]
  · simp
  · simp [testBit_swapK _ _ _ _ hk]

theorem key0 : ∀ x, x < 64 → SwapKey 1 6148914691236517205 x := by decide
theorem key1 : ∀ x, x < 64 → SwapKey 2 3689348814741910323 x := by decide
theorem key2 : ∀ x, x < 64 → SwapKey 4 1085102592571150095 x := by decide
theorem key3 : ∀ x, x < 64 → SwapKey 8 71777214294589695 x := by decide
theorem key4 : ∀ x, x < 64 → SwapKey 16 281470681808895 x := by decide
theorem key5 : ∀ x, x < 64 → SwapKey 32 4294967295 x := by decide

theorem xor_lt64 {x y : Nat} (hx : x < 64) (hy : y < 64) : x ^^^ y < 64 :=
  Nat.xor_lt_two_pow (n := 6) hx hy

theorem bitK_mul_lt (b j s : Nat) (hs : s < 64) : bitK b j * s < 64 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (bitK_le b j) with h | h <;> rw [h] <;> omega

theorem bits_xor : ∀ b, b < 64 → bitK b 5 * 32 ^^^ (bitK b 4 * 16 ^^^ (bitK b 3 * 8 ^^^
    (bitK b 2 * 4 ^^^ (bitK b 1 * 2 ^^^ bitK b 0 * 1)))) = b := by decide

theorem testBit_xl (m b x : Nat) (hb : b < 64) (hx : x < 64) :
    (xl m b).testBit x = m.testBit (x ^^^ b) := by
  unfold xl
  simp only [forceN_eq]
  have l5 := xor_lt64 hx (bitK_mul_lt b 5 32 (by omega))
  have l4 := xor_lt64 l5 (bitK_mul_lt b 4 16 (by omega))
  have l3 := xor_lt64 l4 (bitK_mul_lt b 3 8 (by omega))
  have l2 := xor_lt64 l3 (bitK_mul_lt b 2 4 (by omega))
  have l1 := xor_lt64 l2 (bitK_mul_lt b 1 2 (by omega))
  rw [testBit_stage _ _ _ _ _ _ (key5 _ hx), testBit_stage _ _ _ _ _ _ (key4 _ l5),
    testBit_stage _ _ _ _ _ _ (key3 _ l4), testBit_stage _ _ _ _ _ _ (key2 _ l3),
    testBit_stage _ _ _ _ _ _ (key1 _ l2), testBit_stage _ _ _ _ _ _ (key0 _ l1)]
  simp only [Nat.xor_assoc]
  rw [bits_xor b hb]

theorem smK_cons (b : Nat) (l : List Nat) : smK (b :: l) = smK l ||| xl (smK l) b := by
  change forceN (smK l) (fun m => Nat.lor m (xl m b)) = _
  rw [forceN_eq]
  rfl

theorem spanList_lt (l : List Nat) (hl : ∀ x ∈ l, x < 64) : ∀ y ∈ spanList l, y < 64 := by
  induction l with
  | nil => simp [spanList]
  | cons b l ih =>
    have hb : b < 64 := hl b (by simp)
    have ih := ih (fun x hx => hl x (by simp [hx]))
    intro y hy
    simp only [spanList, List.mem_append, List.mem_map] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact ih y hy
    · exact xor_lt64 (ih z hz) hb

theorem smK_bit (l : List Nat) (hl : ∀ x ∈ l, x < 64) :
    ∀ x, x < 64 → (smK l).testBit x = (spanList l).contains x := by
  induction l with
  | nil =>
    intro x hx
    change (1 : Nat).testBit x = [0].contains x
    rcases x with _ | x
    · rfl
    · rw [Nat.testBit_succ]
      simp
  | cons b l ih =>
    have hb : b < 64 := hl b (by simp)
    have ih := ih (fun x hx => hl x (by simp [hx]))
    intro x hx
    rw [smK_cons, Nat.testBit_or, testBit_xl _ _ _ hb hx, ih x hx, ih _ (xor_lt64 hx hb)]
    apply Bool.eq_iff_iff.mpr
    simp only [spanList, Bool.or_eq_true, List.contains_iff_mem, List.contains_append,
      List.mem_map]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨_, h, by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩
    · rintro (h | ⟨z, hz, rfl⟩)
      · exact Or.inl h
      · right
        rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem memK_smK (l : List Nat) (hl : ∀ x ∈ l, x < 64) (v : Nat) (hv : v < 64) :
    memK (smK l) v = (spanList l).contains v := by
  rw [memK_eq, smK_bit l hl v hv]

def Good (l : List Nat) : Prop := ∀ x ∈ l, x < 64

theorem allL_congr (p q : Nat → Bool) (l : List Nat) (h : ∀ x ∈ l, p x = q x) :
    allL p l = l.all q := by
  rw [allL_eq]
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.all_cons, List.all_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem anyL_congr (p q : Nat → Bool) (l : List Nat) (h : ∀ x ∈ l, p x = q x) :
    anyL p l = l.any q := by
  rw [anyL_eq]
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.any_cons, List.any_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem length_mul (A B : List Nat) : (mul A B).length = B.length := List.length_map _

theorem length_gen (φ ψ l : Nat) : (gen φ ψ l).length = 6 := by
  match l with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | k + 4 => rfl

theorem length_evalW (φ ψ : Nat) (w : List Nat) : (evalW φ ψ w).length = 6 := by
  unfold evalW
  suffices ∀ acc : List Nat, acc.length = 6 →
      (w.foldl (fun acc l => mul acc (gen φ ψ l)) acc).length = 6 from this one rfl
  induction w with
  | nil => exact fun acc h => h
  | cons l w ih =>
    intro acc _
    exact ih _ (by rw [length_mul, length_gen])

theorem length_pow (A : List Nat) (k : Nat) : (pow A k).length = 6 := by
  induction k with
  | zero => rfl
  | succ k ih => exact (length_mul _ _).trans ih

theorem Sm_add {A B : List Nat} (hA : Sm A) (hB : Sm B) : Sm (add A B) := by
  refine ⟨?_, ?_⟩
  · unfold add
    rw [List.length_zipWith]
    exact Nat.le_trans (Nat.min_le_left _ _) hA.1
  · intro x hx
    unfold add at hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.getElem_zipWith]
    exact xor_lt64 (hA.2 _ (List.getElem_mem _)) (hB.2 _ (List.getElem_mem _))

theorem eqModK_eq (Kb : List Nat) (hK : Good Kb) (A B : List Nat) (hA : Sm A) (hB : Sm B)
    (hlA : A.length = 6) (hlB : B.length = 6) :
    eqModK (smK Kb) (packL A) (packL B) = eqMod (spanList Kb) A B := by
  unfold eqModK eqMod
  rw [allC_packL _ 6 A B hA.2 hB.2 hlA hlB]
  have hS := (Sm_add hA hB).2
  rw [← allL_eq]
  exact allL_congr _ _ _ (fun x hx => memK_smK Kb hK x (hS x hx))

theorem invK_eq (Kb : List Nat) (hK : Good Kb) (A : List Nat) (hA : Sm A) :
    invK Kb (smK Kb) (packL A) = invariantUnder Kb (spanList Kb) A := by
  unfold invK invariantUnder
  exact allL_congr _ _ _ (fun b _ => by
    rw [mv_packL A hA, memK_smK Kb hK _ (mulVec_lt A hA.2 b)])

theorem addVK_eq (b : List Nat) (hb : Good b) (v : Nat) (hv : v < 64)
    (k : List Nat → Nat → Bool) : addVK b (smK b) v k = k (addVec b v) (smK (addVec b v)) := by
  unfold addVK addVec
  rw [memK_smK b hb v hv]
  cases h : (spanList b).contains v
  · change forceN (smK b ||| xl (smK b) v) (fun M' => k (v :: b) M') = _
    rw [forceN_eq, ← smK_cons]
    rfl
  · rfl

theorem addVec_good (b : List Nat) (hb : Good b) (v : Nat) (hv : v < 64) : Good (addVec b v) := by
  unfold addVec
  split
  · exact hb
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · exact hb x hx

theorem foldl_addVec_good (l : List Nat) (hl : Good l) (cur : List Nat) (hc : Good cur) :
    Good (l.foldl addVec cur) := by
  induction l generalizing cur with
  | nil => exact hc
  | cons x l ih =>
    exact ih (fun y hy => hl y (by simp [hy])) _ (addVec_good cur hc x (hl x (by simp)))

theorem foldl_addVec_prefix (l cur : List Nat) : ∃ pre, l.foldl addVec cur = pre ++ cur := by
  induction l generalizing cur with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨pre, hp⟩ := ih (addVec cur x)
    rw [List.foldl_cons, hp]
    unfold addVec
    split
    · exact ⟨pre, rfl⟩
    · exact ⟨pre ++ [x], by simp⟩

theorem addAll_eq (src : List Nat) (hs : Good src) (cur : List Nat) (hc : Good cur)
    (k : List Nat → Nat → Bool) :
    addAll src cur (smK cur) k = k (src.foldl addVec cur) (smK (src.foldl addVec cur)) := by
  induction src generalizing cur with
  | nil => rfl
  | cons x src ih =>
    change addVK cur (smK cur) x (fun c' M' => addAll src c' M' k) = _
    rw [addVK_eq cur hc x (hs x (by simp))]
    exact ih (fun y hy => hs y (by simp [hy])) _ (addVec_good cur hc x (hs x (by simp)))

theorem addImgs_eq (A : List Nat) (hA : Sm A) (src : List Nat) (cur : List Nat) (hc : Good cur)
    (k : List Nat → Nat → Bool) :
    addImgs (packL A) src cur (smK cur) k =
      k ((src.map (mulVec A)).foldl addVec cur) (smK ((src.map (mulVec A)).foldl addVec cur)) := by
  induction src generalizing cur with
  | nil => rfl
  | cons x src ih =>
    change forceN (mv (packL A) x) (fun v => addVK cur (smK cur) v
      (fun c' M' => addImgs (packL A) src c' M' k)) = _
    rw [forceN_eq, mv_packL A hA, addVK_eq cur hc _ (mulVec_lt A hA.2 x)]
    exact ih _ (addVec_good cur hc _ (mulVec_lt A hA.2 x))

theorem map_good (A : List Nat) (hA : Sm A) (src : List Nat) : Good (src.map (mulVec A)) := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact mulVec_lt A hA.2 y

theorem closeStep_eq3 (A B C b : List Nat) : closeStep [A, B, C] b =
    List.foldl addVec (List.foldl addVec (List.foldl addVec b (b.map (mulVec A)))
      (b.map (mulVec B))) (b.map (mulVec C)) := by
  unfold closeStep
  simp [List.foldl_append]

theorem closeStep_good (A B C : List Nat) (hA : Sm A) (hB : Sm B) (hC : Sm C) (b : List Nat)
    (hb : Good b) : Good (closeStep [A, B, C] b) := by
  rw [closeStep_eq3]
  exact foldl_addVec_good _ (map_good C hC b) _ (foldl_addVec_good _ (map_good B hB b) _
    (foldl_addVec_good _ (map_good A hA b) _ hb))

theorem stepK_eq (A B C : List Nat) (hA : Sm A) (hB : Sm B) (hC : Sm C) (b : List Nat)
    (hb : Good b) (k : List Nat → Nat → Bool) :
    stepK (packL A) (packL B) (packL C) b (smK b) k =
      k (closeStep [A, B, C] b) (smK (closeStep [A, B, C] b)) := by
  unfold stepK
  rw [addImgs_eq A hA b b hb, addImgs_eq B hB b _ (foldl_addVec_good _ (map_good A hA b) _ hb),
    addImgs_eq C hC b _ (foldl_addVec_good _ (map_good B hB b) _
      (foldl_addVec_good _ (map_good A hA b) _ hb)), closeStep_eq3]

def itr (f : List Nat → List Nat) : Nat → List Nat → List Nat
  | 0, b => b
  | s + 1, b => itr f s (f b)

theorem itr_fixed (f : List Nat → List Nat) (b : List Nat) (h : f b = b) (s : Nat) :
    itr f s b = b := by
  induction s with
  | zero => rfl
  | succ s ih => change itr f s (f b) = b; rw [h, ih]

theorem foldl_range_itr (f : List Nat → List Nat) (s : Nat) (b : List Nat) :
    (List.range s).foldl (fun b _ => f b) b = itr f s b := by
  induction s generalizing b with
  | zero => rfl
  | succ s ih =>
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    exact ih (f b)

theorem iterK_eq (A B C : List Nat) (hA : Sm A) (hB : Sm B) (hC : Sm C) (s : Nat) (b : List Nat)
    (hb : Good b) (k : List Nat → Nat → Bool) :
    iterK (packL A) (packL B) (packL C) s b (smK b) k =
      k (itr (closeStep [A, B, C]) s b) (smK (itr (closeStep [A, B, C]) s b)) := by
  induction s generalizing b with
  | zero => rfl
  | succ s ih =>
    change stepK (packL A) (packL B) (packL C) b (smK b) (fun b' M' =>
      Bool.rec (iterK (packL A) (packL B) (packL C) s b' M' k) (k b (smK b))
        (Nat.beq b'.length b.length)) = _
    rw [stepK_eq A B C hA hB hC b hb]
    change _ = k (itr (closeStep [A, B, C]) s (closeStep [A, B, C] b)) _
    cases h : Nat.beq (closeStep [A, B, C] b).length b.length
    · exact ih _ (closeStep_good A B C hA hB hC b hb)
    · have hl := Nat.beq_eq.mp h
      obtain ⟨pre, hp⟩ := foldl_addVec_prefix
        ((([A, B, C].flatMap fun g => b.map (mulVec g)))) b
      have hfix : closeStep [A, B, C] b = b := by
        unfold closeStep
        rw [hp]
        unfold closeStep at hl
        rw [hp, List.length_append] at hl
        have : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this, List.nil_append]
      change k b (smK b) = _
      rw [hfix]
      simp only [itr_fixed _ b hfix]

theorem itr_good (f : List Nat → List Nat) (hf : ∀ b, Good b → Good (f b)) (s : Nat)
    (b : List Nat) (hb : Good b) : Good (itr f s b) := by
  induction s generalizing b with
  | zero => exact hb
  | succ s ih => exact ih _ (hf b hb)

theorem addAll_nil (src : List Nat) (hs : Good src) (k : List Nat → Nat → Bool) :
    addAll src [] 1 k = k (src.foldl addVec []) (smK (src.foldl addVec [])) :=
  addAll_eq src hs [] (fun _ h => nomatch h) k

theorem gen0 (φ ψ : Nat) : gen φ ψ 0 = chartY φ := rfl
theorem gen1 (φ ψ : Nat) : gen φ ψ 1 = chartD ψ := rfl
theorem gen2 (φ ψ : Nat) : gen φ ψ 2 = chartT := rfl

theorem Sm6_evalW (φ ψ : Nat) (w : List Nat) : Sm (evalW φ ψ w) := (evalWK_eq φ ψ w).2

theorem checkBK_eq (φ ψ : Nat) (Kb : List Nat) (hK : Good Kb) (m : Nat) (g : List Nat) :
    checkBK (lettersK φ ψ) Kb m g = checkB φ ψ Kb m g := by
  obtain ⟨hE1, hE2⟩ := evalWK_eq φ ψ g
  obtain ⟨hP1, hP2⟩ := powK_packL hE2 m
  have hkm : xorC 6 (packL (pow (evalW φ ψ g) m)) oneK = add (pow (evalW φ ψ g) m) one :=
    xorC_packL 6 _ _ hP2.2 Sm_one.2 (length_pow _ _) rfl
  have hS := Sm_add hP2 Sm_one
  have hlen : (add (pow (evalW φ ψ g) m) one).length = 6 := by
    unfold add
    rw [List.length_zipWith, length_pow]
    rfl
  unfold checkBK checkB
  simp only [forceN_eq, genK_letters, gen0, gen1, gen2]
  rw [hE1, hP1, hkm, closeBasis, foldl_range_itr]
  generalize hq : add (pow (evalW φ ψ g) m) one = q at hS hlen
  have hst : Good (Kb ++ q) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hK x hx
    · exact hS.2 x hx
  rw [addAll_nil (Kb ++ q) hst, iterK_eq _ _ _ (Sm_chartY φ) (Sm_chartD ψ) Sm_chartT 7 _
    (foldl_addVec_good _ hst [] (fun _ h => nomatch h))]
  have hWg := itr_good _ (closeStep_good _ _ _ (Sm_chartY φ) (Sm_chartD ψ) Sm_chartT) 7 _
    (foldl_addVec_good _ hst [] (fun _ h => nomatch h))
  generalize itr (closeStep [chartY φ, chartD ψ, chartT]) 7 ((Kb ++ q).foldl addVec []) = Wb at hWg
  have e1 : allL (fun b => memK (smK Wb) (mv (packL (chartY φ)) b) &&
      memK (smK Wb) (mv (packL (chartD ψ)) b) && memK (smK Wb) (mv (packL chartT) b)) Wb =
      Wb.all fun b => [chartY φ, chartD ψ, chartT].all fun g =>
        (spanList Wb).contains (mulVec g b) := by
    refine allL_congr _ _ _ (fun b _ => ?_)
    rw [mv_packL _ (Sm_chartY φ), mv_packL _ (Sm_chartD ψ), mv_packL _ Sm_chartT,
      memK_smK Wb hWg _ (mulVec_lt _ (Sm_chartY φ).2 b),
      memK_smK Wb hWg _ (mulVec_lt _ (Sm_chartD ψ).2 b),
      memK_smK Wb hWg _ (mulVec_lt _ Sm_chartT.2 b)]
    simp [Bool.and_assoc]
  have e2 : allL (fun x => memK (smK Wb) x) q = q.all fun x => (spanList Wb).contains x :=
    allL_congr _ _ _ (fun x hx => memK_smK Wb hWg x (hS.2 x hx))
  have e3 : allL (fun b => memK (smK Kb) (mv (packL q) b)) Wb =
      Wb.all fun b => (spanList Kb).contains (mulVec q b) :=
    allL_congr _ _ _ (fun b _ => by rw [mv_packL q hS, memK_smK Kb hK _ (mulVec_lt q hS.2 b)])
  have e4 : anyL (fun x => !memK (smK Kb) x) q = q.any fun x => !(spanList Kb).contains x :=
    anyL_congr _ _ _ (fun x hx => by rw [memK_smK Kb hK x (hS.2 x hx)])
  rw [e1, e2, e3, e4]

theorem Sm_pow {A : List Nat} (hA : Sm A) (k : Nat) : Sm (pow A k) := (powK_packL hA k).2

theorem powK_packL' {A : List Nat} (hA : Sm A) (k : Nat) : powK (packL A) k = packL (pow A k) :=
  (powK_packL hA k).1

theorem length_chartT : chartT.length = 6 := rfl
theorem length_one : one.length = 6 := rfl

theorem checkCK_eq (φ ψ : Nat) (Kb : List Nat) (hK : Good Kb) (a m : Nat) (cw : List Nat) :
    checkCK (lettersK φ ψ) Kb a m cw = checkC φ ψ (spanList Kb) a m cw := by
  unfold checkCK checkC
  have hc := Sm6_evalW φ ψ cw
  have hi := Sm6_evalW φ ψ (invW cw)
  have hY := Sm_chartY φ
  simp only [forceN_eq, genK_letters, gen0, gen2, (evalWK_eq φ ψ cw).1,
    (evalWK_eq φ ψ (invW cw)).1, oneK_eq]
  rw [mulK_packL hY hi, mulK_packL hc (Sm_mul hY hi), mulK_packL hY (Sm_mul hc (Sm_mul hY hi)),
    mulK_packL Sm_chartT hc, mulK_packL hc Sm_chartT, mulK_packL hc hi]
  have hx := Sm_mul hY (Sm_mul hc (Sm_mul hY hi))
  rw [powK_packL' hx, powK_packL' (Sm_pow hx a)]
  have l1 : ∀ A B : List Nat, B.length = 6 → (mul A B).length = 6 := fun A B h =>
    (length_mul A B).trans h
  rw [eqModK_eq Kb hK _ _ (Sm_mul Sm_chartT hc) (Sm_mul hc Sm_chartT) (l1 _ _ (length_evalW _ _ _))
      (l1 _ _ length_chartT),
    eqModK_eq Kb hK _ _ (Sm_mul hc hi) Sm_one (l1 _ _ (length_evalW _ _ _)) length_one,
    eqModK_eq Kb hK _ _ (Sm_pow hx a) Sm_one (length_pow _ _) length_one,
    eqModK_eq Kb hK _ _ (Sm_pow (Sm_pow hx a) m) Sm_one (length_pow _ _) length_one]

theorem packL_inj (A B : List Nat) (hA : ∀ x ∈ A, x < 64) (hB : ∀ x ∈ B, x < 64)
    (hl : A.length = B.length) (h : packL A = packL B) : A = B := by
  induction A generalizing B with
  | nil =>
    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at hl
    exact hl.symm
  | cons a A ih =>
    obtain ⟨b, B, rfl⟩ := List.exists_cons_of_length_eq_add_one hl.symm
    have ha : a < 64 := hA a (by simp)
    have hb : b < 64 := hB b (by simp)
    rw [packL_cons, packL_cons] at h
    have e1 : a = b := by
      have := congrArg (· % 64) h
      rwa [dig_mod _ ha, dig_mod _ hb] at this
    have e2 : packL A = packL B := by
      have := congrArg (· / 64) h
      rwa [dig_div _ ha, dig_div _ hb] at this
    rw [e1, ih B (fun x hx => hA x (by simp [hx])) (fun x hx => hB x (by simp [hx]))
      (by simpa using hl) e2]

@[expose] noncomputable def kerR (P k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun x ih => forceN ih fun r =>
    Nat.lor r (Nat.shiftLeft (Bool.rec 0 1 (Nat.beq (mv P x) 0)) x)) k

theorem kerR_succ (P k : Nat) : kerR P (k + 1) =
    forceN (kerR P k) (fun r => r ||| ((Bool.rec 0 1 (Nat.beq (mv P k) 0) : Nat) <<< k)) := rfl

theorem kerK_bit (P k x : Nat) :
    (kerR P k).testBit x = (decide (x < k) && Nat.beq (mv P x) 0) := by
  induction k with
  | zero => change (0 : Nat).testBit x = _; simp
  | succ k ih =>
    rw [kerR_succ, forceN_eq]
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy x k with hx | rfl | hx
    · have : ¬ k ≤ x := by omega
      simp [hx, this, Nat.lt_succ_of_lt hx]
    · cases Nat.beq (mv P x) 0 <;> simp
    · have h1 : ¬ x < k := by omega
      have h2 : ¬ x < k + 1 := by omega
      have h4 : Nat.testBit 1 (x - k) = false := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (n := x - k) (by omega)
        rw [hj, Nat.testBit_succ]
        simp
      cases Nat.beq (mv P k) 0
      · simp [h1, h2]
      · simp [h1, h2, h4]

theorem kerK_testBit (P x : Nat) (hx : x < 64) : (kerK P).testBit x = Nat.beq (mv P x) 0 := by
  change (kerR P 64).testBit x = _
  rw [kerK_bit]
  simp [hx]

theorem checkS_of (n φ ψ : Nat) (Kb : List Nat) (hK : Good Kb) (s : Mat × Mat × Mat) (θ : Mat)
    (h : checkSK n φ ψ Kb s θ = true) : checkS n φ ψ (spanList Kb) s θ = true := by
  unfold checkSK at h
  simp only [forceN_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hl⟩, hθ⟩, hs1⟩, hs2⟩, hs3⟩, ⟨⟨⟨⟨hY, hD⟩, hT⟩, hker⟩, hspan⟩⟩ := h
  have hn : n ≤ 6 := Nat.le_of_ble_eq_true hn
  have hl : θ.length = 6 := Nat.eq_of_beq_eq_true hl
  have hθ : ∀ x ∈ θ, x < 2 ^ n := by
    rw [allL_eq, List.all_eq_true] at hθ
    exact fun x hx => Nat.le_of_ble_eq_true (hθ x hx)
  have h64 : 2 ^ n ≤ 64 := Nat.pow_le_pow_right (by omega) hn
  have hSθ : Sm θ := ⟨by omega, fun x hx => Nat.lt_of_lt_of_le (hθ x hx) h64⟩
  have sm : ∀ A : List Nat, smallM A = true → Sm A := by
    intro A hA
    unfold smallM at hA
    rw [Bool.and_eq_true, allL_eq, List.all_eq_true] at hA
    exact ⟨Nat.le_of_ble_eq_true hA.1, fun x hx => Nat.le_of_ble_eq_true (hA.2 x hx)⟩
  have hs1 := sm _ hs1
  have hs2 := sm _ hs2
  have hs3 := sm _ hs3
  have eqm : ∀ (C S : List Nat), Sm C → Sm S → C.length = 6 →
      Nat.beq (mulK (packL θ) (packL C)) (mulK (packL S) (packL θ)) = true →
      (C.map (mulVec θ) == θ.map (mulVec S)) = true := by
    intro C S hC hS hlC hb
    rw [mulK_packL hSθ hC, mulK_packL hS hSθ] at hb
    have := packL_inj _ _ (Sm_mul hSθ hC).2 (Sm_mul hS hSθ).2
      (by rw [length_mul, length_mul, hlC, hl]) (Nat.eq_of_beq_eq_true hb)
    exact beq_iff_eq.mpr this
  have hker : kerK (packL θ) = smK Kb := Nat.eq_of_beq_eq_true hker
  have hspan : smK θ % 2 ^ 2 ^ n = 2 ^ 2 ^ n - 1 := Nat.eq_of_beq_eq_true hspan
  unfold checkS
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨beq_iff_eq.mpr hl, List.all_eq_true.mpr fun x hx => decide_eq_true (hθ x hx)⟩,
    eqm _ _ (Sm_chartY φ) hs1 rfl hY⟩, eqm _ _ (Sm_chartD ψ) hs2 rfl hD⟩,
    eqm _ _ Sm_chartT hs3 rfl hT⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    have hx : x < 64 := List.mem_range.mp hx
    have e := congrArg (fun M => Nat.testBit M x) hker
    rw [kerK_testBit _ _ hx, smK_bit Kb hK x hx, mv_packL θ hSθ] at e
    rw [← e]
    cases hb : Nat.beq (mulVec θ x) 0
    · simp [Nat.ne_of_beq_eq_false hb]
    · simp [Nat.eq_of_beq_eq_true hb]
  · rw [List.all_eq_true]
    intro v hv
    have hv : v < 2 ^ n := List.mem_range.mp hv
    have e := congrArg (fun M => Nat.testBit M v) hspan
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, smK_bit θ hSθ.2 v (by omega)] at e
    simpa [hv] using e

theorem memberOk_of (surv : List (Mat × Mat × Mat)) (n : Nat) (Kb : List Nat) (φ ψ : Nat)
    (w : List Nat) (hK : Good Kb) (h : memberOkK surv n Kb φ ψ w = true) :
    memberOk surv n Kb φ ψ w = true := by
  unfold memberOkK at h
  split at h
  · rw [forceN_eq, checkBK_eq _ _ _ hK] at h
    exact h
  · rw [forceN_eq, checkCK_eq _ _ _ hK] at h
    exact h
  · rename_i i θ
    unfold memberOk
    split at h
    · rename_i s hs
      simp only [hs]
      exact checkS_of _ _ _ _ hK _ _ h
    · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true

theorem zipAll_of (surv : List (Mat × Mat × Mat)) (n : Nat) :
    ∀ (ms : List (List Nat × Nat × Nat)) (d : List Nat), (∀ m ∈ ms, Good m.1) →
      zipAllK surv n ms d = true →
      (ms.length == d.length &&
        (List.zipWith (fun m x => memberOk surv n m.1 m.2.1 m.2.2 (unpack 64 x)) ms d).all id) =
        true
  | [], [] => fun _ _ => rfl
  | [], _ :: _ => fun _ h => absurd h Bool.false_ne_true
  | _ :: _, [] => fun _ h => absurd h Bool.false_ne_true
  | m :: ms, x :: d => fun hg h => by
    change (memberOkK surv n m.1 m.2.1 m.2.2 (unpack 64 x) && zipAllK surv n ms d) = true at h
    rw [Bool.and_eq_true] at h
    have ih := zipAll_of surv n ms d (fun m' hm' => hg m' (by simp [hm'])) h.2
    have hm := memberOk_of surv n m.1 m.2.1 m.2.2 _ (hg m (by simp)) h.1
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_cons, List.zipWith_cons_cons,
      List.all_cons, id] at ih ⊢
    exact ⟨by rw [ih.1], hm, ih.2⟩

theorem mem_members {n : Nat} {m : List Nat × Nat × Nat} (h : m ∈ members n) :
    m.1 ∈ kList (6 - n) := by
  unfold members at h
  rw [List.mem_flatMap] at h
  obtain ⟨Kb, hKb, hm⟩ := h
  split at hm
  · simp only [List.mem_flatMap, List.mem_map] at hm
    obtain ⟨φ, -, ψ, -, rfl⟩ := hm
    exact hKb
  · simp at hm

theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      ih (fun y hy => h y (by simp [hy]))]

theorem kList_good (r : Nat) : ∀ Kb ∈ kList r, Good Kb := by
  match r with
  | 0 => intro Kb hK x hx; simp [kList] at hK; subst hK; simp at hx
  | 1 =>
    intro Kb hK x hx
    simp only [kList, List.mem_filterMap, List.mem_range] at hK
    obtain ⟨a, ha, hK⟩ := hK
    split at hK
    · cases hK
      simp at hx
      omega
    · cases hK
  | 2 =>
    intro Kb hK x hx
    simp only [kList, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hK
    obtain ⟨a, ha, b, hb, hK⟩ := hK
    split at hK
    · cases hK
      simp at hx
      omega
    · cases hK
  | r + 3 => intro Kb hK; simp [kList] at hK

theorem kListK_eq (r : Nat) : kListK r = kList r := by
  match r with
  | 0 => rfl
  | 1 => decide +kernel
  | 2 => decide +kernel
  | r + 3 => rfl

theorem condTK_eq (Kb : List Nat) (hK : Good Kb) : condTK Kb (smK Kb) = condT Kb (spanList Kb) := by
  unfold condTK condT kOk
  rw [invK_eq Kb hK _ Sm_chartT, oneK_eq, xorC_packL 6 chartT one Sm_chartT.2 Sm_one.2 rfl rfl]
  have hS := (Sm_add Sm_chartT Sm_one).2
  rw [allL_congr _ (fun x => !(spanList Kb).contains x) _ (fun x hx => by
      rw [memK_smK Kb hK x (by simp at hx; omega)]),
    anyL_congr _ (fun x => !(spanList Kb).contains x) _ (fun x hx => by
      rw [memK_smK Kb hK x (hS x hx)])]

theorem membersK_eq (n : Nat) : membersK n = members n := by
  unfold membersK members
  rw [flatMapR_eq]
  change (kListK (6 - n)).flatMap _ = _
  rw [kListK_eq]
  refine flatMap_congr' _ _ _ (fun Kb hKb => ?_)
  have hK := kList_good _ Kb hKb
  rw [forceN_eq, condTK_eq Kb hK]
  cases condT Kb (spanList Kb)
  · rfl
  · simp only [if_true, flatMapR_eq, mapR_eq, filterR_eq, ← List.range_eq_range',
      invK_eq Kb hK _ (Sm_chartY _), invK_eq Kb hK _ (Sm_chartD _), condY, condD]
    rfl

theorem check_of_checkK (surv : List (Mat × Mat × Mat)) (n : Nat) (data : List Nat)
    (h : checkK surv n data = true) : check surv n data = true := by
  unfold checkK at h
  rw [membersK_eq] at h
  exact zipAll_of surv n (members n) data
    (fun m hm => kList_good _ _ (mem_members hm)) h

end CFSG.Certificates.Kernel.RouteCK
