module

public import Certificates.Data.CFSGNative.Fi23.Tr
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG.KS.Fi23Tr

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

@[expose] def dEl {G : Type*} [Group G] (a b : G) : G :=
  ((dWord.map fun x => if x = 0 then a else b).prod) ^ 7

section

variable {G X : Type*} [Group G] [MulAction G X] {S : Nat → X}

@[expose] def Moves (S : Nat → X) (T : Table) (g : G) : Prop :=
  ∀ m < 137632, ap T m < 137632 ∧ S (ap T m) = g • S m

theorem ap_compT_lt {n : Nat} (P Q : Table) {i : Nat} (hi : i < n) :
    ap (compT n P Q) i = ap P (ap Q i) := by
  unfold compT ap
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem moves_compT {P Q : Table} {g h : G} (hP : Moves S P g) (hQ : Moves S Q h) :
    Moves S (compT 137632 P Q) (g * h) := by
  intro m hm
  rw [ap_compT_lt _ _ hm]
  obtain ⟨q1, q2⟩ := hQ m hm
  obtain ⟨p1, p2⟩ := hP _ q1
  exact ⟨p1, by rw [p2, q2, mul_smul]⟩

theorem moves_idT : Moves S (idT 137632) (1 : G) := by
  intro m hm
  have e : ap (idT 137632) m = m := by
    unfold idT ap
    rw [getElem!_pos _ _ (by simpa using hm), Array.getElem_ofFn, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  rw [e, one_smul]
  exact ⟨hm, rfl⟩

theorem moves_powT {P : Table} {g : G} (hP : Moves S P g) : ∀ e, Moves S (powT 137632 e P) (g ^ e)
  | 0 => by rw [pow_zero]; exact moves_idT
  | e + 1 => by
    rw [pow_succ']
    exact moves_compT hP (moves_powT hP e)

theorem moves_word {A B : Table} {a b : G} (hA : Moves S A a) (hB : Moves S B b) :
    ∀ w : List Nat, Moves S (w.foldr (fun x T => compT 137632 (if x = 0 then A else B) T)
      (idT 137632)) (w.map fun x => if x = 0 then a else b).prod
  | [] => by
    rw [List.foldr_nil, List.map_nil, List.prod_nil]
    exact moves_idT
  | x :: w => by
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    refine moves_compT ?_ (moves_word hA hB w)
    by_cases hx : x = 0
    · rw [if_pos hx, if_pos hx]
      exact hA
    · rw [if_neg hx, if_neg hx]
      exact hB

theorem trAct_conj {O : WOrbit} {o : TrOrb} {a b : G} (c : Nat → G)
    (hpa : ∀ k < 137632, ap o.pa k < 137632 ∧ S (ap o.pa k) = a • S k)
    (hpb : ∀ k < 137632, ap o.pb k < 137632 ∧ S (ap o.pb k) = b • S k)
    (ha : a * a = 1) (hb : b ^ 3 = 1)
    (hc : ∀ k, c k = if 0 < k ∧ ap O.par k < k then
      (if ap O.lab k = 1 then a else b) * c (ap O.par k) * (if ap O.lab k = 1 then a else b)⁻¹
      else dEl a b) :
    ∀ k, ∀ m < 137632, trAct O o (trD o) (trBi o) k m < 137632 ∧
      S (trAct O o (trD o) (trBi o) k m) = c k • S m := by
  have hA : Moves S o.pa a := hpa
  have hB : Moves S o.pb b := hpb
  have hbi : Moves S (trBi o) b⁻¹ := by
    have e : b * b = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      rw [pow_succ, pow_two] at hb
      exact hb
    rw [← e]
    exact moves_compT hB hB
  have hD : Moves S (trD o) (dEl a b) := moves_powT (moves_word hA hB dWord) 7
  have hai : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one]
    exact ha
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro m hm
    unfold trAct
    rw [treeAct.eq_def, hc k]
    by_cases h : 0 < k ∧ ap O.par k < k
    · rw [dite_eq_left h, if_pos h]
      by_cases hl : ap O.lab k = 1
      · rw [if_pos (beq_iff_eq.2 hl), if_pos hl]
        obtain ⟨a1, a2⟩ := hA m hm
        obtain ⟨i1, i2⟩ := ih _ h.2 _ a1
        unfold trAct at i1 i2
        obtain ⟨b1, b2⟩ := hA _ i1
        refine ⟨b1, ?_⟩
        rw [b2, i2, a2, hai, ← mul_smul, ← mul_smul]
      · rw [if_neg (fun e => hl (beq_iff_eq.1 e)), if_neg hl]
        obtain ⟨a1, a2⟩ := hbi m hm
        obtain ⟨i1, i2⟩ := ih _ h.2 _ a1
        unfold trAct at i1 i2
        obtain ⟨b1, b2⟩ := hB _ i1
        refine ⟨b1, ?_⟩
        rw [b2, i2, a2, ← mul_smul, ← mul_smul]
    · rw [dite_eq_right h, if_neg h]
      exact hD m hm

end

end CFSG.KS.Fi23Tr
