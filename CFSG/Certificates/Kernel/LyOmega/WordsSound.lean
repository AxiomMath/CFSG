module

public import CFSG.Certificates.Kernel.LyOmega.Sound
public import Certificates.Data.Kernel.LyOmega.Words
public import CFSG.Sporadic.Fi23.SlpSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm
open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Fi23 (slpG slpG_eq)

theorem lcanon_eq {X Y : ℕ} (hX : LCanon 12 111 111 X) (hY : LCanon 12 111 111 Y)
    (h : bigM X = bigM Y) : X = Y := by
  have hl : ∀ i < 111, ∀ j < 111, X / 2 ^ (12 * 111 * i + 12 * j) % 2 ^ 12 =
      Y / 2 ^ (12 * 111 * i + 12 * j) % 2 ^ 12 := by
    intro i hi j hj
    have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    simp only [bigM, ent] at e
    have e2 : 1332 * i + 12 * j = 12 * 111 * i + 12 * j := by ring
    rw [e2] at e
    have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
    rwa [Nat.mod_eq_of_lt (hX.2 i hi j hj), Nat.mod_eq_of_lt (hY.2 i hi j hj)] at this
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 12 * 111 * 111
  · have hi : k / 12 / 111 < 111 := by omega
    have hj : k / 12 % 111 < 111 := Nat.mod_lt _ (by norm_num)
    have e := hl _ hi _ hj
    have key : ∀ Z : ℕ, Z.testBit k =
        (Z / 2 ^ (12 * 111 * (k / 12 / 111) + 12 * (k / 12 % 111)) % 2 ^ 12).testBit (k % 12) := by
      intro Z
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      have h1 : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
      have h2 : k % 12 + (12 * 111 * (k / 12 / 111) + 12 * (k / 12 % 111)) = k := by omega
      simp [h1, h2]
    rw [key X, key Y, e]
  · have hXk : X < 2 ^ k := lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hYk : Y < 2 ^ k := lt_of_lt_of_le hY.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hXk, Nat.testBit_lt_two_pow hYk]

section Words

variable {G : Type*} [Group G]

@[expose] def seedL (a b : G) (z : ℤ) : G :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

@[expose] def letG (s : ℤ → G) (P : ℕ → G) (j : ℕ) (z : ℤ) : G :=
  if z.natAbs ≤ 2 then s z
  else if z.natAbs - 3 < j then (if 0 < z then P (z.natAbs - 3) else (P (z.natAbs - 3))⁻¹) else 1

theorem slpG_letG (s : ℤ → G) (words : Array (List ℤ)) (j : ℕ) :
    slpG s words j = wordG (letG s (slpG s words) j) words[j]! := by
  rw [slpG_eq]
  rfl

variable (C : BConsts) (R : ℕ → G → Prop)
  (hmul : ∀ {X Y : ℕ} {g h : G}, R X g → R Y h → R (fMul C X Y) (g * h)) (hone : R C.ONEF 1)
  {A B Bi : ℕ} {a b : G} (hA : R A a) (hAi : R A a⁻¹) (hB : R B b) (hBi : R Bi b⁻¹)

include hone hA hAi hB hBi in
theorem slpLet_sound (vals : List (ℕ × ℕ)) (j : ℕ) (P : ℕ → G)
    (hv : ∀ i < j, R (vals.getD i (C.ONEF, C.ONEF)).1 (P i) ∧
      R (vals.getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹) (z : ℤ) :
    R (slpLet C A B Bi vals j z).1 (letG (seedL a b) P j z) ∧
      R (slpLet C A B Bi vals j z).2 (letG (seedL a b) P j z)⁻¹ := by
  by_cases h1 : z = 1
  · subst h1
    simp only [slpLet, letG, seedL, if_true]
    norm_num
    exact ⟨hA, hAi⟩
  by_cases hm1 : z = -1
  · subst hm1
    simp only [slpLet, letG, seedL]
    norm_num
    exact ⟨hAi, by simpa using hA⟩
  by_cases h2 : z = 2
  · subst h2
    simp only [slpLet, letG, seedL]
    norm_num
    exact ⟨hB, hBi⟩
  by_cases ha : z.natAbs ≤ 2
  · simp only [slpLet, letG, seedL, if_neg h1, if_neg hm1, if_neg h2, if_pos ha]
    exact ⟨hBi, by rw [inv_inv]; exact hB⟩
  by_cases hj : z.natAbs - 3 < j
  · by_cases hz : 0 < z
    · simp only [slpLet, letG, if_neg h1, if_neg hm1, if_neg h2, if_neg ha, if_pos hj, if_pos hz]
      exact hv _ hj
    · simp only [slpLet, letG, if_neg h1, if_neg hm1, if_neg h2, if_neg ha, if_pos hj, if_neg hz,
        inv_inv]
      exact ⟨(hv _ hj).2, (hv _ hj).1⟩
  · simp only [slpLet, letG, if_neg h1, if_neg hm1, if_neg h2, if_neg ha, if_neg hj, inv_one]
    exact ⟨hone, hone⟩

include hmul in
theorem foldl_sound (L : ℤ → G) (f : ℤ → ℕ × ℕ) (w : List ℤ)
    (hf : ∀ z ∈ w, R (f z).1 (L z) ∧ R (f z).2 (L z)⁻¹) :
    ∀ (p : ℕ × ℕ) (g : G), R p.1 g → R p.2 g⁻¹ →
      R (List.foldl (fun p z => (fun q : ℕ × ℕ => (fMul C p.1 q.1, fMul C q.2 p.2)) (f z)) p w).1
          (g * wordG L w) ∧
        R (List.foldl (fun p z => (fun q : ℕ × ℕ => (fMul C p.1 q.1, fMul C q.2 p.2)) (f z)) p w).2
          (g * wordG L w)⁻¹ := by
  induction w with
  | nil =>
    intro p g h1 h2
    simpa [wordG] using ⟨h1, h2⟩
  | cons z w ih =>
    intro p g h1 h2
    have hz := hf z List.mem_cons_self
    have := ih (fun z' hz' => hf z' (List.mem_cons_of_mem _ hz'))
      (fMul C p.1 (f z).1, fMul C (f z).2 p.2) (g * L z) (hmul h1 hz.1)
      (by rw [mul_inv_rev]; exact hmul hz.2 h2)
    simpa [wordG, List.map_cons, List.prod_cons, mul_assoc] using this

include hmul hone hA hAi hB hBi in
theorem wordLanes_sound (vals : List (ℕ × ℕ)) (j : ℕ) (P : ℕ → G)
    (hv : ∀ i < j, R (vals.getD i (C.ONEF, C.ONEF)).1 (P i) ∧
      R (vals.getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹) (w : List ℤ) :
    R (wordLanes C A B Bi vals j w).1 (wordG (letG (seedL a b) P j) w) ∧
      R (wordLanes C A B Bi vals j w).2 (wordG (letG (seedL a b) P j) w)⁻¹ := by
  have := foldl_sound C R hmul (letG (seedL a b) P j) (slpLet C A B Bi vals j) w
    (fun z _ => slpLet_sound C R hone hA hAi hB hBi vals j P hv z) (C.ONEF, C.ONEF) 1 hone
    (by rw [inv_one]; exact hone)
  simpa [wordLanes] using this

theorem getD_append_lt {α : Type*} (l : List α) (x d : α) {i : ℕ} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

include hmul hone hA hAi hB hBi in
theorem slpVals_sound (ws : List (List ℤ)) :
    (slpVals C A B Bi ws).length = ws.length ∧ ∀ i < ws.length,
      R ((slpVals C A B Bi ws).getD i (C.ONEF, C.ONEF)).1 (slpG (seedL a b) ws.toArray i) ∧
        R ((slpVals C A B Bi ws).getD i (C.ONEF, C.ONEF)).2 (slpG (seedL a b) ws.toArray i)⁻¹ := by
  set P : ℕ → G := slpG (seedL a b) ws.toArray with hP
  have key : ∀ (rest : List (List ℤ)) (vals : List (ℕ × ℕ)),
      vals.length + rest.length = ws.length →
      (∀ k < rest.length, ws[vals.length + k]! = rest[k]!) →
      (∀ i < vals.length, R (vals.getD i (C.ONEF, C.ONEF)).1 (P i) ∧
        R (vals.getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹) →
      (slpRun C A B Bi vals rest).length = ws.length ∧ ∀ i < ws.length,
        R ((slpRun C A B Bi vals rest).getD i (C.ONEF, C.ONEF)).1 (P i) ∧
          R ((slpRun C A B Bi vals rest).getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹ := by
    intro rest
    induction rest with
    | nil =>
      intro vals hlen _ hv
      simp only [List.length_nil, add_zero] at hlen
      refine ⟨by simpa [slpRun] using hlen, fun i hi => ?_⟩
      simpa [slpRun] using hv i (by omega)
    | cons w rest ih =>
      intro vals hlen hrest hv
      have hw : ws[vals.length]! = w := by simpa using hrest 0 (by simp)
      have hnew : R (wordLanes C A B Bi vals vals.length w).1 (P vals.length) ∧
          R (wordLanes C A B Bi vals vals.length w).2 (P vals.length)⁻¹ := by
        have h := wordLanes_sound C R hmul hone hA hAi hB hBi vals vals.length P hv w
        have e : P vals.length = wordG (letG (seedL a b) P vals.length) w := by
          rw [hP, slpG_letG, List.getElem!_toArray, hw]
        rw [e]
        exact h
      have := ih (vals ++ [wordLanes C A B Bi vals vals.length w])
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
        (fun k hk => by
          have := hrest (k + 1) (by simp; omega)
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm 1 k] using this)
        (fun i hi => by
          simp only [List.length_append, List.length_cons, List.length_nil] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [getD_append_lt _ _ _ hi]
            exact hv i hi
          · simpa [List.getD_eq_getElem?_getD] using hnew)
      simpa [slpRun] using this
  have := key ws [] (by simp) (fun k _ => by simp) (fun i hi => absurd hi (Nat.not_lt_zero _))
  simpa [slpVals] using this

@[expose] def relLetter (s : ℤ → G) (P : ℕ → G) (z : ℤ) : G :=
  if z.natAbs ≤ 2 then s z
  else if 0 < z then P (z.natAbs - 3) else (P (z.natAbs - 3))⁻¹

include hmul hone hA hAi hB hBi in
theorem relLanes_sound (vals : List (ℕ × ℕ)) (P : ℕ → G)
    (hv : ∀ i < vals.length, R (vals.getD i (C.ONEF, C.ONEF)).1 (P i) ∧
      R (vals.getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹)
    (hP : ∀ i, vals.length ≤ i → P i = 1) (w : List ℤ) :
    R (relLanes C A B Bi vals w) (wordG (relLetter (seedL a b) P) w) := by
  have e : relLetter (seedL a b) P = letG (seedL a b) P vals.length := by
    funext z
    unfold relLetter letG
    by_cases h2 : z.natAbs ≤ 2
    · simp [h2]
    · by_cases h3 : z.natAbs - 3 < vals.length
      · simp [h2, h3]
      · simp [h2, h3, hP (z.natAbs - 3) (by omega)]
  rw [e]
  exact (wordLanes_sound C R hmul hone hA hAi hB hBi vals vals.length P hv w).1

end Words

section Hom

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 111) (Fin 111) (ZMod 5))

structure LRep (X : ℕ) (g : G) : Prop where
  canon : LCanon 12 111 111 X
  eq : bigM X = φ g

variable {φ}

theorem LRep.mul {C : BConsts} (hC : bConstsOK C = true) {X Y : ℕ} {g h : G} (hX : LRep φ X g)
    (hY : LRep φ Y h) : LRep φ (fMul C X Y) (g * h) := by
  obtain ⟨c, e⟩ := fMul_sound hC hX.canon hY.canon
  exact ⟨c, by rw [e, hX.eq, hY.eq, map_mul]⟩

variable {C : BConsts} (hC : bConstsOK C = true)
  (hone : LCanon 12 111 111 C.ONEF ∧ bigM C.ONEF = 1)
  {A B Bi : ℕ} {a b : G} (hA : LRep φ A a) (hAi : LRep φ A a⁻¹) (hB : LRep φ B b)
  (hBi : LRep φ Bi b⁻¹)

include hone in
theorem LRep.one : LRep φ C.ONEF 1 := ⟨hone.1, by rw [hone.2, map_one]⟩

include hC hone hA hAi hB hBi in
theorem slpVals_hom (ws : List (List ℤ)) :
    (slpVals C A B Bi ws).length = ws.length ∧ ∀ i < ws.length,
      LRep φ ((slpVals C A B Bi ws).getD i (C.ONEF, C.ONEF)).1 (slpG (seedL a b) ws.toArray i) ∧
        LRep φ ((slpVals C A B Bi ws).getD i (C.ONEF, C.ONEF)).2
          (slpG (seedL a b) ws.toArray i)⁻¹ :=
  slpVals_sound C (LRep φ) (fun hX hY => LRep.mul hC hX hY) (LRep.one hone) hA hAi hB hBi ws

include hC hone hA hAi hB hBi in
theorem relLanes_hom (vals : List (ℕ × ℕ)) (P : ℕ → G)
    (hv : ∀ i < vals.length, LRep φ (vals.getD i (C.ONEF, C.ONEF)).1 (P i) ∧
      LRep φ (vals.getD i (C.ONEF, C.ONEF)).2 (P i)⁻¹)
    (hP : ∀ i, vals.length ≤ i → P i = 1) (w : List ℤ) :
    LRep φ (relLanes C A B Bi vals w) (wordG (relLetter (seedL a b) P) w) :=
  relLanes_sound C (LRep φ) (fun hX hY => LRep.mul hC hX hY) (LRep.one hone) hA hAi hB hBi vals
    P hv hP w

include hC hone in
theorem fPow_hom {X : ℕ} {g : G} (hX : LRep φ X g) : ∀ n : ℕ, LRep φ (fPow C X n) (g ^ n)
  | 0 => by simpa [fPow] using LRep.one hone
  | n + 1 => by
    have := LRep.mul hC (fPow_hom hX n) hX
    rw [← pow_succ] at this
    exact this

end Hom

end CFSG.KS.LyOm
