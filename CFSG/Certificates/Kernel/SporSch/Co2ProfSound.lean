module

public import Certificates.Data.Kernel.SporSch.Co2Prof
public import CFSG.Certificates.Kernel.Spor.Loops

set_option exponentiation.threshold 600

public section

namespace CFSG.KS.Co2P

open CFSG.KC.Enum CFSG.KS.Co2M

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : ℕ) : Bool.rec (motive := fun _ => ℕ) e t c = if c then t else e := by
  cases c <;> rfl

theorem fiK_zero (p : ℕ → Bool) (X : ℕ) : fiK p 0 X = 0 := rfl

theorem fiK_succ (p : ℕ → Bool) (n X : ℕ) :
    fiK p (n + 1) X = if p X then 0 else fiK p n (mw X X) + 1 := by
  change strictN X (fun X => Bool.rec (motive := fun _ => ℕ) (Nat.succ (fiK p n (mw X X))) 0 (p X))
    = _
  rw [strictN_eq, nIf_eq]

theorem fiK_le (p : ℕ → Bool) : ∀ n X, fiK p n X ≤ n
  | 0, _ => le_rfl
  | n + 1, X => by
    rw [fiK_succ]
    split
    · omega
    · have := fiK_le p n (mw X X)
      omega

theorem isIZ_eq (Z X : ℕ) : isIZ Z X = (isI X || Nat.beq (Nat.mod X (Nat.pow 2 484)) Z) := by
  unfold isIZ
  cases isI X <;> rfl

theorem cK_eq (Z : ℕ) : ∀ n X, cK Z n X = 8 * fiK isI n X + fiK (isIZ Z) n X
  | 0, _ => rfl
  | n + 1, X => by
    have e : cK Z (n + 1) X = strictN X fun X => Bool.rec (motive := fun _ => ℕ)
        (strictN (mw X X) fun X2 => Bool.rec (motive := fun _ => ℕ)
          (Nat.add (cK Z n X2) 9) (Nat.mul 8 (Nat.succ (fiK isI n X2))) (isIZ Z X)) 0 (isI X) :=
      rfl
    rw [e, strictN_eq, nIf_eq, strictN_eq, nIf_eq, fiK_succ, fiK_succ, cK_eq Z n]
    by_cases h1 : isI X = true
    · simp [h1, isIZ_eq]
    · have h1' : isI X = false := by simpa using h1
      by_cases h2 : isIZ Z X = true
      · simp only [h1', h2, Bool.false_eq_true, ↓reduceIte]
        change 8 * (fiK isI n (mw X X) + 1) = 8 * (fiK isI n (mw X X) + 1) + 0
        omega
      · have h2' : isIZ Z X = false := by simpa using h2
        simp only [h1', h2', Bool.false_eq_true, ↓reduceIte]
        change 8 * fiK isI n (mw X X) + fiK (isIZ Z) n (mw X X) + 9 =
          8 * (fiK isI n (mw X X) + 1) + (fiK (isIZ Z) n (mw X X) + 1)
        omega

theorem keyM_eq (Y Z A B : ℕ) :
    keyM Y Z A B = 8 * fiK isI 6 (mw (mw B A) Y) + fiK (isIZ Z) 6 (mw (mw B A) Y) :=
  cK_eq Z 6 _

theorem keyM_digits (Y Z A B : ℕ) : keyM Y Z A B / 8 < 7 ∧ keyM Y Z A B % 8 < 7 := by
  rw [keyM_eq]
  have h1 := fiK_le isI 6 (mw (mw B A) Y)
  have h2 := fiK_le (isIZ Z) 6 (mw (mw B A) Y)
  omega

@[expose] noncomputable def Hs (l : List ℕ) : ℕ := (l.map incK).sum

theorem Hs_append (l m : List ℕ) : Hs (l ++ m) = Hs l + Hs m := by
  simp [Hs]

theorem Hs_cons (k : ℕ) (l : List ℕ) : Hs (k :: l) = incK k + Hs l := by
  simp [Hs]

theorem hB_eq (Y Z A : ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    hB Y Z A l acc = acc + Hs (l.map (keyM Y Z A))
  | [], acc => by simp [hB, Hs]
  | B :: l, acc => by
    change strictN (Nat.add acc (incK (keyM Y Z A B))) (hB Y Z A l) = _
    rw [strictN_eq, hB_eq Y Z A l, List.map_cons, Hs_cons]
    change acc + incK (keyM Y Z A B) + _ = _
    omega

theorem hA_eq (Y Z : ℕ) (T₁ : List ℕ) : ∀ (T₀ : List ℕ) (acc : ℕ),
    hA Y Z T₁ T₀ acc = acc + Hs (T₀.flatMap fun A => T₁.map (keyM Y Z A))
  | [], acc => by simp [hA, Hs]
  | A :: T₀, acc => by
    change strictN (hB Y Z A T₁ acc) (hA Y Z T₁ T₀) = _
    rw [strictN_eq, hA_eq Y Z T₁ T₀, hB_eq, List.flatMap_cons, Hs_append]
    omega

theorem sum_lt (c : ℕ → ℕ) : ∀ m, (∀ j < m, c j < 2 ^ 16) →
    (∑ i ∈ Finset.range m, c i * 2 ^ (16 * i)) < 2 ^ (16 * m)
  | 0, _ => by simp
  | m + 1, hc => by
    rw [Finset.sum_range_succ]
    have ih := sum_lt c m fun j hj => hc j (by omega)
    have hm := hc m (by omega)
    have e : 2 ^ (16 * (m + 1)) = 2 ^ (16 * m) * 2 ^ 16 := by rw [← pow_add, Nat.mul_succ]
    rw [e]
    have : c m * 2 ^ (16 * m) + 2 ^ (16 * m) ≤ 2 ^ (16 * m) * 2 ^ 16 := by
      have := Nat.mul_le_mul_right (2 ^ (16 * m)) (Nat.succ_le_of_lt hm)
      rw [Nat.succ_mul] at this
      linarith
    omega

theorem field_sum (c : ℕ → ℕ) : ∀ m, (∀ j < m, c j < 2 ^ 16) → ∀ j < m,
    (∑ i ∈ Finset.range m, c i * 2 ^ (16 * i)) / 2 ^ (16 * j) % 2 ^ 16 = c j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, hc, j, hj => by
    rw [Finset.sum_range_succ]
    have hlt := sum_lt c m fun j hj => hc j (by omega)
    rcases Nat.lt_or_ge j m with hjm | hjm
    · have e : c m * 2 ^ (16 * m) = 2 ^ (16 * j) * ((c m * 2 ^ (16 * (m - j - 1))) * 2 ^ 16) := by
        have : 16 * m = 16 * j + 16 + 16 * (m - j - 1) := by omega
        rw [this, pow_add, pow_add]
        ring
      rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
      exact field_sum c m (fun j hj => hc j (by omega)) j hjm
    · have hjm' : j = m := by omega
      subst hjm'
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.mod_eq_of_lt (hc j (by omega))]

theorem fieldK_eq (H j : ℕ) : fieldK H j = H / 2 ^ (16 * j) % 2 ^ 16 := by
  unfold fieldK
  change (H >>> (16 * j)) &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

@[expose] def dg (k j : ℕ) : ℕ := (if k / 8 = j then 1 else 0) + (if 7 + k % 8 = j then 1 else 0)

theorem incK_eq {k : ℕ} (hk : k / 8 < 7 ∧ k % 8 < 7) :
    incK k = ∑ j ∈ Finset.range 14, dg k j * 2 ^ (16 * j) := by
  unfold dg
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega)]
  unfold incK
  change 1 <<< (16 * (k / 8)) + 1 <<< (16 * (7 + k % 8)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul]

@[expose] def cnt (l : List ℕ) (j : ℕ) : ℕ := (l.map fun k => dg k j).sum

theorem Hs_eq : ∀ (l : List ℕ), (∀ k ∈ l, k / 8 < 7 ∧ k % 8 < 7) →
    Hs l = ∑ j ∈ Finset.range 14, cnt l j * 2 ^ (16 * j)
  | [], _ => by simp [Hs, cnt]
  | k :: l, hl => by
    rw [Hs_cons, Hs_eq l fun k hk => hl k (List.mem_cons_of_mem _ hk),
      incK_eq (hl k List.mem_cons_self), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cnt, List.map_cons, List.sum_cons]
    ring

theorem cnt_le (l : List ℕ) (j : ℕ) : cnt l j ≤ 2 * l.length := by
  induction l with
  | nil => simp [cnt]
  | cons k l ih =>
    simp only [cnt, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have : dg k j ≤ 2 := by unfold dg; split_ifs <;> omega
    omega

theorem cnt_lo (l : List ℕ) (hl : ∀ k ∈ l, k % 8 < 7) {e : ℕ} (he : e < 7) :
    cnt l e = (l.map (· / 8)).count e := by
  induction l with
  | nil => simp [cnt]
  | cons k l ih =>
    simp only [cnt, List.map_cons, List.sum_cons, List.count_cons] at ih ⊢
    rw [ih fun k hk => hl k (List.mem_cons_of_mem _ hk)]
    unfold dg
    have : ¬ 7 + k % 8 = e := by omega
    simp only [this, ↓reduceIte, Nat.add_zero, beq_iff_eq]
    split_ifs <;> omega

theorem cnt_hi (l : List ℕ) {e : ℕ} (he : e < 7) (hl : ∀ k ∈ l, k / 8 < 7) :
    cnt l (7 + e) = (l.map (· % 8)).count e := by
  induction l with
  | nil => simp [cnt]
  | cons k l ih =>
    simp only [cnt, List.map_cons, List.sum_cons, List.count_cons] at ih ⊢
    rw [ih fun k hk => hl k (List.mem_cons_of_mem _ hk)]
    unfold dg
    have : ¬ k / 8 = 7 + e := by have := hl k List.mem_cons_self; omega
    simp only [this, ↓reduceIte, Nat.zero_add, beq_iff_eq]
    split_ifs <;> omega

theorem rowK_counts {l : List ℕ} (hl : ∀ k ∈ l, k / 8 < 7 ∧ k % 8 < 7) (hlen : l.length < 32768)
    {row : List ℕ} (h : rowK (Hs l) row = true) :
    ∀ e < 6, (l.map (· / 8)).count e = row.getD (6 + e) 0 ∧
      (l.map (· % 8)).count e = row.getD e 0 := by
  intro e he
  have hb := allN_spec h e he
  rw [bAnd_iff, Nat.beq_eq, Nat.beq_eq] at hb
  simp only [Nat.add_eq] at hb
  have hc : ∀ j < 14, cnt l j < 2 ^ 16 := fun j _ => by
    have := cnt_le l j
    omega
  rw [Hs_eq l hl, fieldK_eq, fieldK_eq] at hb
  rw [field_sum _ 14 hc e (by omega), field_sum _ 14 hc (7 + e) (by omega)] at hb
  rw [← cnt_lo l (fun k hk => (hl k hk).2) (by omega : e < 7),
    ← cnt_hi l (by omega : e < 7) fun k hk => (hl k hk).1]
  exact ⟨hb.1, hb.2⟩

end CFSG.KS.Co2P

end
