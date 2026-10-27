module

public import Certificates.Data.Kernel.A6EOneN

public section

namespace CFSG.Quasithin.H13.A6EOne

open CFSG.QuasithinUnique.A6Facts.Core
open CFSG.QuasithinUnique.Setup.X3Aut (invC)

theorem decK_succ (k x : Nat) : decK (k + 1) x = x % 16 :: decK k (x / 16) := rfl

theorem decK_zero (x : Nat) : decK 0 x = [] := rfl

theorem length_decK (k x : Nat) : (decK k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [decK_succ, ih]

theorem getD_decK (k x j : Nat) :
    (decK k x).getD j 0 = if j < k then x / 16 ^ j % 16 else 0 := by
  induction k generalizing x j with
  | zero => simp [decK_zero]
  | succ k ih =>
    cases j with
    | zero => simp [decK_succ]
    | succ j =>
      simp only [decK_succ, List.getD_cons_succ, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]
      by_cases h : j < k
      · simp [h, Nat.mul_comm]
      · simp [h]

theorem decK_eq_iff (k x y : Nat) : decK k x = decK k y ↔ x % 16 ^ k = y % 16 ^ k := by
  induction k generalizing x y with
  | zero => simp [decK_zero, Nat.mod_one]
  | succ k ih =>
    simp only [decK_succ, List.cons.injEq, ih]
    rw [Nat.pow_succ, Nat.mul_comm (16 ^ k) 16, Nat.mod_mul, Nat.mod_mul]
    have hx := Nat.mod_lt x (show 16 > 0 by decide)
    have hy := Nat.mod_lt y (show 16 > 0 by decide)
    omega

theorem decK_encL (c : List Nat) (hc : ∀ a ∈ c, a < 16) : decK c.length (encL c) = c := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    have ha : a < 16 := hc a (List.mem_cons_self ..)
    have h := ih fun b hb => hc b (List.mem_cons_of_mem _ hb)
    change decK (c.length + 1) (Nat.add a (Nat.mul 16 (encL c))) = a :: c
    rw [decK_succ]
    have h1 : Nat.add a (Nat.mul 16 (encL c)) % 16 = a := by
      change (a + 16 * encL c) % 16 = a
      omega
    have h2 : Nat.add a (Nat.mul 16 (encL c)) / 16 = encL c := by
      change (a + 16 * encL c) / 16 = encL c
      omega
    rw [h1, h2, h]

theorem dec_encL (c : List Nat) (hl : c.length = 10) (hc : ∀ a ∈ c, a < 16) :
    dec (encL c) = c := by
  have h := decK_encL c hc
  rw [hl] at h
  exact h

theorem laneN_eq (x j : Nat) : laneN x j = (dec x).getD j 0 := by
  rw [dec, getD_decK]
  unfold laneN
  by_cases h : j < 10
  · have hb : Nat.blt j 10 = true := by simpa using h
    simp only [hb, cond_true, h, if_true]
    change x >>> (4 * j) % 16 = x / 16 ^ j % 16
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  · have hb : Nat.blt j 10 = false := by
      cases hh : Nat.blt j 10
      · rfl
      · exact absurd (by simpa using hh) h
    simp [hb, h]

theorem getD_dec_lt (x j : Nat) : (dec x).getD j 0 < 16 := by
  rw [dec, getD_decK]
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem dec_mulN (x y : Nat) : dec (mulN x y) = cmul (dec x) (dec y) := by
  have hm : (dec y).map (laneN x) = cmul (dec x) (dec y) := by
    unfold cmul
    exact List.map_congr_left fun j _ => laneN_eq x j
  unfold mulN
  rw [hm]
  apply dec_encL
  · simp [cmul, dec, length_decK]
  · intro a ha
    simp only [cmul, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact getD_dec_lt x j

theorem dec_invN (x : Nat) : dec (invN x) = invC (dec x) := by
  unfold invN
  apply dec_encL
  · simp [invC]
  · intro a ha
    simp only [invC, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    have h := List.idxOf_le_length (l := decK 10 x) (a := j)
    rw [length_decK] at h
    change List.idxOf j (decK 10 x) < 16
    omega

theorem dec_cidN : dec cidN = cid := by decide +kernel

theorem eqN_eq (x y : Nat) : eqN x y = (dec x == dec y) := by
  have h : (dec x == dec y) = decide (x % 16 ^ 10 = y % 16 ^ 10) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact decK_eq_iff 10 x y
  rw [h]
  unfold eqN
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact Iff.rfl

theorem memN_eq (L : List Nat) : memN L = fun x => (L.map dec).contains (dec x) := by
  funext x
  unfold memN
  rw [List.contains_map]
  exact List.any_congr rfl fun a => eqN_eq x a

theorem getD_map_comm {α β : Type} (f : α → β) (L : List α) (i : Nat) (d : α) :
    f (L.getD i d) = (L.map f).getD i (f d) := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i <;> simp [ih]

theorem pslN_dec : pslN.map dec = pslLit := by decide +kernel

theorem repsInvN_dec : repsInvN.map dec = autRepsInv := by decide +kernel

theorem dec_conjN (x e : Nat) : dec (conjN x e) = conjC (dec x) (dec e) := by
  simp only [conjN, conjC, dec_mulN, dec_invN]

theorem dec_commN (x y : Nat) : dec (commN x y) = commC (dec x) (dec y) := by
  simp only [commN, commC, dec_mulN, dec_invN]

theorem inXN_eq (I : List Nat) (c : Nat) : inXN I c = inX I (dec c) := by
  unfold inXN inX
  simp only [memN_eq, dec_mulN, getD_map_comm dec repsInvN, repsInvN_dec, dec_cidN, pslN_dec]

theorem isSubN_eq (L : List Nat) : isSubN L = isSubC (L.map dec) := by
  unfold isSubN isSubC
  simp only [memN_eq, dec_mulN, dec_invN, dec_cidN, List.all_map, Function.comp_def]

theorem commAllN_eq (c : Nat) (E : List Nat) : commAllN c E = commutesAll (dec c) (E.map dec) := by
  unfold commAllN commutesAll
  simp only [eqN_eq, dec_mulN, List.all_map, Function.comp_def]

theorem chkW_eq (g : Grp) (D : Nat → Nat) (hD : ∀ n, dc n = dec (D n)) (w : Wit) :
    g.chkW w = g.chkWN D w := by
  have hc : ∀ L : List Nat, codes L = (L.map D).map dec := fun L => by
    simp only [codes, List.map_map]
    exact List.map_congr_left fun n _ => hD n
  have hS : g.Sc = (g.ScN D).map dec := hc g.S
  have hE : ∀ j, g.Ec j = (g.EcN D j).map dec := fun j => hc _
  unfold Grp.chkW Grp.chkWN
  simp only [hc, hS, hE, memN_eq, isSubN_eq, inXN_eq, commAllN_eq, dec_conjN, dec_commN,
    dec_invN, List.all_map, List.any_map, List.filter_map, List.length_map, Function.comp_def]

theorem chkWit_eq (g : Grp) (D : Nat → Nat) (hD : ∀ n, dc n = dec (D n)) :
    g.chkWit = g.chkWitN D := by
  unfold Grp.chkWit Grp.chkWitN
  exact List.all_congr rfl fun w => chkW_eq g D hD w

theorem dc_eq_DofT (T : Nat → Nat) (h : autL = (List.range 1440).map fun n => dec (T n)) (n : Nat) :
    dc n = dec (DofT T n) := by
  unfold dc DofT
  rw [h]
  by_cases hn : n < 1440
  · have hb : Nat.blt n 1440 = true := by simpa using hn
    rw [hb, cond_true, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
    rfl
  · have hb : Nat.blt n 1440 = false := by
      cases hh : Nat.blt n 1440
      · rfl
      · exact absurd (by simpa using hh) hn
    rw [hb, cond_false, dec_cidN, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp; omega

end CFSG.Quasithin.H13.A6EOne

end
