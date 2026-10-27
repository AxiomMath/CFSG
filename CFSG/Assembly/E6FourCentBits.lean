module

public import CFSG.Assembly.E6FourCentChecker
public import Mathlib.Logic.Relation
import Mathlib.Tactic.Set
import Batteries.Tactic.Init
import Mathlib.Tactic.Push

public section

namespace CFSG.Assembly.E6FourCentChk

@[expose] def Reach (A S : Nat) : Nat → Nat → Prop :=
  Relation.ReflTransGen fun a b => b < 72 ∧ S.testBit b = true ∧ A.testBit (72 * a + b) = true

@[expose] def permAt (P j : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 7 j)) 127

private lemma M72_eq : M72 = 2 ^ 72 - 1 := by decide

private lemma M72_testBit (j : Nat) : M72.testBit j = decide (j < 72) := by
  rw [M72_eq, Nat.testBit_two_pow_sub_one]

private lemma lt_two_pow_iff_testBit (m n : Nat) :
    m < 2 ^ n ↔ ∀ i, n ≤ i → m.testBit i = false := by
  constructor
  · intro h i hi
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_of_le (by decide : 1 < 2) hi))
  · intro h
    exact Nat.lt_pow_two_of_testBit m h

private lemma testBit_log2_gt (m : Nat) (hm : m ≠ 0) {i : Nat} (hi : m.log2 < i) :
    m.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_of_le (by decide : 1 < 2) (by omega)))

private lemma log2_lt_of_lt (m : Nat) (hm : m ≠ 0) {n : Nat} (hmn : m < 2 ^ n) : m.log2 < n :=
  (Nat.log2_lt hm).mpr hmn

private lemma one_testBit (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  change (2 ^ 0 : Nat).testBit i = decide (i = 0)
  rw [Nat.testBit_two_pow]
  by_cases h : i = 0
  · subst h; rfl
  · have h0 : ¬ (0 = i) := fun e => h e.symm
    rw [decide_eq_false_iff_not.mpr h0, decide_eq_false_iff_not.mpr h]

private lemma testBit_shiftLeft_one (t i : Nat) : (1 <<< t).testBit i = decide (i = t) := by
  rw [Nat.testBit_shiftLeft, one_testBit]
  rcases Nat.lt_trichotomy i t with h | h | h
  · have hnt : ¬ t ≤ i := Nat.not_le.mpr h
    have hne : i ≠ t := Nat.ne_of_lt h
    simp [hnt, hne]
  · subst h; simp
  · have hle : t ≤ i := Nat.le_of_lt h
    have hne : i ≠ t := Nat.ne_of_gt h
    have hsub : i - t ≠ 0 := by omega
    simp [hle, hne, hsub]

private lemma testBit_xor_pow_two (m t : Nat) (hm : m.testBit t = true) (i : Nat) :
    (m ^^^ (1 <<< t)).testBit i = (m.testBit i && decide (i ≠ t)) := by
  rw [Nat.testBit_xor, testBit_shiftLeft_one]
  by_cases h : i = t
  · subst h; simp [hm]
  · simp [h]

private lemma xor_pow_two_lt (m t : Nat) (hm : m.testBit t = true)
    (hgt : ∀ i, t < i → m.testBit i = false) : m ^^^ (1 <<< t) < 2 ^ t := by
  rw [lt_two_pow_iff_testBit]
  intro i hi
  rw [testBit_xor_pow_two m t hm i]
  by_cases hit : i = t
  · subst hit; rw [hm]; simp
  · have hti : t < i := by omega
    rw [hgt i hti]; simp [hit]

private lemma land_shiftRight_M72_testBit (A t j : Nat) :
    (Nat.land (Nat.shiftRight A (Nat.mul 72 t)) M72).testBit j
      = (A.testBit (72 * t + j) && decide (j < 72)) := by
  rw [Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_shiftRight, M72_testBit]
  rfl

private lemma one_shiftLeft_lt {k : Nat} (hk : k < 72) : Nat.shiftLeft 1 k < 2 ^ 72 := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hk

private lemma one_shiftLeft_reach (A S k : Nat) :
    ∀ j, (Nat.shiftLeft 1 k).testBit j = true → Reach A S k j := by
  intro j hj
  have hj_eq : j = k := by
    have hd : (Nat.shiftLeft 1 k).testBit j = decide (j = k) := by
      rw [Nat.shiftLeft_eq', testBit_shiftLeft_one]
    rw [hd] at hj
    exact of_decide_eq_true hj
  rw [hj_eq]
  exact Relation.ReflTransGen.refl

private lemma xor_M72_lt (m : Nat) (hm : m < 2 ^ 72) : m ^^^ M72 < 2 ^ 72 := by
  rw [lt_two_pow_iff_testBit]
  intro i hi
  rw [Nat.testBit_xor, M72_testBit, (lt_two_pow_iff_testBit m 72).mp hm i hi]
  simp [Nat.not_lt.mpr hi]

private lemma expand_succ (A n fr acc : Nat) :
    expand A (n + 1) fr acc =
      bif Nat.beq fr 0 then acc else
        expand A n (Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr)))
          (Nat.lor acc (Nat.land (Nat.shiftRight A (Nat.mul 72 (Nat.log2 fr))) M72)) := rfl

private lemma bfs_succ (A S n vis fr : Nat) :
    bfs A S (n + 1) vis fr =
      bif Nat.beq fr 0 then vis else
        bfs A S n (Nat.lor vis (Nat.land (Nat.land (expand A 72 fr 0) S) (Nat.xor vis M72)))
          (Nat.land (Nat.land (expand A 72 fr 0) S) (Nat.xor vis M72)) := rfl

private lemma mapMaskP_succ (P n m acc : Nat) :
    mapMaskP P (n + 1) m acc =
      bif Nat.beq m 0 then acc else
        mapMaskP P n (Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m)))
          (Nat.lor acc (Nat.shiftLeft 1
            (Nat.land (Nat.shiftRight P (Nat.mul 7 (Nat.log2 m))) 127))) := rfl

private lemma rowsOK_succ (S n rem : Nat) :
    rowsOK S (n + 1) rem =
      bif Nat.beq rem 0 then true else
        (rowOK S (compOf adjLit S (Nat.log2 rem)) &&
          rowsOK S n (Nat.land rem (Nat.xor (compOf adjLit S (Nat.log2 rem)) M72))) := rfl

private lemma hasFive_nil (R c : Nat) : hasFive R [] c = Nat.ble 5 c := rfl

private lemma hasFive_cons (R m c : Nat) (ms : List Nat) :
    hasFive R (m :: ms) c =
      bif Nat.ble 5 c then true
      else hasFive R ms (bif Nat.beq (Nat.land R m) R then c + 1 else c) := rfl

private lemma testBit_expand_aux (A j : Nat) (hj : j < 72) :
    ∀ n fr acc, fr < 2 ^ n →
      ((expand A n fr acc).testBit j = true ↔
        acc.testBit j = true ∨
          ∃ i, i < n ∧ fr.testBit i = true ∧ A.testBit (72 * i + j) = true) := by
  intro n
  induction n with
  | zero =>
      intro fr acc hfr
      have hfr0 : fr = 0 := by
        have : fr < 1 := by simpa using hfr
        omega
      subst hfr0
      simp only [expand]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i, hi, _, _⟩)
        · exact h
        · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro fr acc hfr
      rw [expand_succ]
      by_cases hf0 : fr = 0
      · subst hf0
        rw [Nat.beq_refl]
        simp only [Bool.cond_true]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨i, hi, hbit, _⟩)
          · exact h
          · rw [Nat.zero_testBit] at hbit; exact Bool.noConfusion hbit
      · have hbeq : Nat.beq fr 0 = false := by
          cases h : Nat.beq fr 0 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true h) hf0
        rw [hbeq]
        simp only [Bool.cond_false]
        have ht_bit : fr.testBit (Nat.log2 fr) = true := Nat.testBit_log2 hf0
        have ht_lt : Nat.log2 fr < n + 1 := log2_lt_of_lt fr hf0 hfr
        have ht_le : Nat.log2 fr ≤ n := Nat.lt_succ_iff.mp ht_lt
        have hfr'_lt : Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr)) < 2 ^ n :=
          Nat.lt_of_lt_of_le
            (xor_pow_two_lt fr (Nat.log2 fr) ht_bit (fun i hi => testBit_log2_gt fr hf0 hi))
            (Nat.pow_le_pow_of_le (by decide : 1 < 2) ht_le)
        have hacc' : (Nat.lor acc (Nat.land (Nat.shiftRight A (Nat.mul 72 (Nat.log2 fr))) M72)).testBit j
            = (acc.testBit j || A.testBit (72 * Nat.log2 fr + j)) := by
          rw [Nat.lor_eq, Nat.testBit_or, land_shiftRight_M72_testBit,
              decide_eq_true_eq.mpr hj, Bool.and_true]
        have hmask_bit (i : Nat) : (Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr))).testBit i
            = (fr.testBit i && decide (i ≠ Nat.log2 fr)) :=
          testBit_xor_pow_two fr (Nat.log2 fr) ht_bit i
        have ih' := ih (Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr)))
          (Nat.lor acc (Nat.land (Nat.shiftRight A (Nat.mul 72 (Nat.log2 fr))) M72)) hfr'_lt
        rw [ih', hacc', Bool.or_eq_true_iff]
        constructor
        · rintro ((hacc | hadj) | ⟨i, hi, hbi, hadji⟩)
          · exact Or.inl hacc
          · exact Or.inr ⟨Nat.log2 fr, ht_lt, ht_bit, hadj⟩
          · have hbi' : fr.testBit i = true := by
              have h' : (fr.testBit i && decide (i ≠ Nat.log2 fr)) = true := by
                rw [← hmask_bit i]; exact hbi
              exact (Bool.and_eq_true_iff.mp h').1
            exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hbi', hadji⟩
        · rintro (hacc | ⟨i, hi, hbi, hadji⟩)
          · exact Or.inl (Or.inl hacc)
          · by_cases hit : i = Nat.log2 fr
            · subst hit
              exact Or.inl (Or.inr hadji)
            · have hlt : i < Nat.log2 fr := by
                rcases Nat.lt_or_gt_of_ne hit with h | h
                · exact h
                · exfalso
                  have hf : fr.testBit i = false := testBit_log2_gt fr hf0 h
                  rw [hbi] at hf
                  exact Bool.noConfusion hf
              have hbi' : (Nat.xor fr (Nat.shiftLeft 1 (Nat.log2 fr))).testBit i = true := by
                rw [hmask_bit i, hbi, decide_eq_true_eq.mpr hit, Bool.and_true]
              exact Or.inr ⟨i, by omega, hbi', hadji⟩

theorem testBit_expand (A n fr acc j : Nat) (hj : j < 72) (hfr : fr < 2 ^ n) :
    (expand A n fr acc).testBit j = true ↔
      acc.testBit j = true ∨
        ∃ i, i < n ∧ fr.testBit i = true ∧ A.testBit (72 * i + j) = true :=
  testBit_expand_aux A j hj n fr acc hfr

private lemma bfs_invariant (A S k : Nat) :
    ∀ n vis fr, vis < 2 ^ 72 → fr < 2 ^ 72 →
      (∀ j, fr.testBit j = true → vis.testBit j = true) →
      (∀ j, vis.testBit j = true → Reach A S k j) →
      (bfs A S n vis fr) < 2 ^ 72 ∧
      (∀ j, vis.testBit j = true → (bfs A S n vis fr).testBit j = true) ∧
      (∀ j, (bfs A S n vis fr).testBit j = true → Reach A S k j) := by
  intro n
  induction n with
  | zero =>
      intro vis fr hvis _ _ hreach
      simp only [bfs]
      exact ⟨hvis, fun j hj => hj, hreach⟩
  | succ n ih =>
      intro vis fr hvis hfr hsub hreach
      rw [bfs_succ]
      by_cases hf0 : fr = 0
      · subst hf0
        rw [Nat.beq_refl]
        simp only [Bool.cond_true]
        exact ⟨hvis, fun j hj => hj, hreach⟩
      · have hbeq : Nat.beq fr 0 = false := by
          cases h : Nat.beq fr 0 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true h) hf0
        rw [hbeq]
        simp only [Bool.cond_false]
        set nx := Nat.land (Nat.land (expand A 72 fr 0) S) (Nat.xor vis M72) with hnx
        have hvisxor : vis ^^^ M72 < 2 ^ 72 := xor_M72_lt vis hvis
        have hnx_lt : nx < 2 ^ 72 := by
          rw [hnx, Nat.land_eq, Nat.xor_eq]
          exact Nat.lt_of_le_of_lt Nat.and_le_right hvisxor
        have hnx_reach : ∀ j, nx.testBit j = true → Reach A S k j := by
          intro j hj
          have hj72 : j < 72 := by
            by_contra hge
            have hle : 72 ≤ j := Nat.le_of_not_lt hge
            have hf : nx.testBit j = false := (lt_two_pow_iff_testBit nx 72).mp hnx_lt j hle
            rw [hf] at hj
            exact Bool.noConfusion hj
          have hbit : (Nat.land (Nat.land (expand A 72 fr 0) S) (Nat.xor vis M72)).testBit j
              = true := by
            rw [← hnx]; exact hj
          rw [Nat.land_eq, Nat.testBit_and, Nat.land_eq, Nat.testBit_and, Nat.xor_eq,
              Nat.testBit_xor, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hbit
          obtain ⟨⟨hexp, hS⟩, _⟩ := hbit
          rcases (testBit_expand A 72 fr 0 j hj72 hfr).mp hexp with h0 | ⟨i, _, hfri, hadj⟩
          · rw [Nat.zero_testBit] at h0; exact Bool.noConfusion h0
          · exact Relation.ReflTransGen.tail (hreach i (hsub i hfri))
              ⟨hj72, hS, hadj⟩
        have hvis' : Nat.lor vis nx < 2 ^ 72 := by
          rw [Nat.lor_eq]; exact Nat.or_lt_two_pow hvis hnx_lt
        have hsub' : ∀ j, nx.testBit j = true → (Nat.lor vis nx).testBit j = true := by
          intro j hj
          rw [Nat.lor_eq, Nat.testBit_or, hj, Bool.or_true]
        have hreach' : ∀ j, (Nat.lor vis nx).testBit j = true → Reach A S k j := by
          intro j hj
          rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true_iff] at hj
          rcases hj with h | h
          · exact hreach j h
          · exact hnx_reach j h
        obtain ⟨h1, h2, h3⟩ := ih (Nat.lor vis nx) nx hvis' hnx_lt hsub' hreach'
        refine ⟨h1, fun j hj => h2 j ?_, h3⟩
        rw [Nat.lor_eq, Nat.testBit_or, hj, Bool.true_or]

theorem compOf_lt (A S k : Nat) (hk : k < 72) : compOf A S k < 2 ^ 72 := by
  have hk72 := one_shiftLeft_lt hk
  have h := (bfs_invariant A S k 12 (Nat.shiftLeft 1 k) (Nat.shiftLeft 1 k) hk72 hk72
    (fun _ hj => hj) (one_shiftLeft_reach A S k)).1
  simpa only [compOf] using h

theorem compOf_self (A S k : Nat) (hk : k < 72) : (compOf A S k).testBit k = true := by
  have hk72 := one_shiftLeft_lt hk
  have hbit : (Nat.shiftLeft 1 k).testBit k = true := by
    rw [Nat.shiftLeft_eq', testBit_shiftLeft_one, decide_eq_true_eq.mpr rfl]
  have h := (bfs_invariant A S k 12 (Nat.shiftLeft 1 k) (Nat.shiftLeft 1 k) hk72 hk72
    (fun _ hj => hj) (one_shiftLeft_reach A S k)).2.1
  simpa only [compOf] using h k hbit

theorem compOf_sound (A S k : Nat) (hk : k < 72) {j : Nat} (hj : (compOf A S k).testBit j = true) :
    Reach A S k j := by
  have hk72 := one_shiftLeft_lt hk
  have h := (bfs_invariant A S k 12 (Nat.shiftLeft 1 k) (Nat.shiftLeft 1 k) hk72 hk72
    (fun _ hj => hj) (one_shiftLeft_reach A S k)).2.2
  exact h j (by simpa only [compOf] using hj)

theorem closedOK_spec (A S c : Nat) (hc : c < 2 ^ 72) (h : closedOK A S c = true) {a b : Nat}
    (ha : c.testBit a = true) (hb : b < 72) (hbS : S.testBit b = true)
    (hab : A.testBit (72 * a + b) = true) : c.testBit b = true := by
  by_contra hcb
  have hcb' : c.testBit b = false := by
    cases h' : c.testBit b with
    | false => rfl
    | true => exact absurd h' hcb
  have ha72 : a < 72 := by
    by_contra hge
    have hle : 72 ≤ a := Nat.le_of_not_lt hge
    have hf : c.testBit a = false := (lt_two_pow_iff_testBit c 72).mp hc a hle
    rw [hf] at ha
    exact Bool.noConfusion ha
  have hexp : (expand A 72 c 0).testBit b = true :=
    (testBit_expand A 72 c 0 b hb hc).mpr (Or.inr ⟨a, ha72, ha, hab⟩)
  have hbit : (Nat.land (Nat.land (expand A 72 c 0) S) (Nat.xor c M72)).testBit b = true := by
    rw [Nat.land_eq, Nat.testBit_and, Nat.land_eq, Nat.testBit_and, Nat.xor_eq, Nat.testBit_xor]
    rw [hexp, hbS, hcb', M72_testBit, decide_eq_true_eq.mpr hb]
    rfl
  have hzero : (Nat.land (Nat.land (expand A 72 c 0) S) (Nat.xor c M72)) = 0 :=
    Nat.eq_of_beq_eq_true h
  rw [hzero, Nat.zero_testBit] at hbit
  exact Bool.noConfusion hbit

theorem compOf_iff (A S k : Nat) (hk : k < 72) (h : closedOK A S (compOf A S k) = true) (j : Nat) :
    (compOf A S k).testBit j = true ↔ Reach A S k j := by
  constructor
  · intro hj
    exact compOf_sound A S k hk hj
  · intro hj
    unfold Reach at hj
    induction hj with
    | refl => exact compOf_self A S k hk
    | tail hab hbc ih =>
        exact closedOK_spec A S (compOf A S k) (compOf_lt A S k hk) h ih hbc.1 hbc.2.1 hbc.2.2

private lemma testBit_mapMaskP_aux (P j : Nat) :
    ∀ n m acc, m < 2 ^ n →
      ((mapMaskP P n m acc).testBit j = true ↔
        acc.testBit j = true ∨ ∃ i, i < n ∧ m.testBit i = true ∧ permAt P i = j) := by
  intro n
  induction n with
  | zero =>
      intro m acc hm
      have hm0 : m = 0 := by
        have : m < 1 := by simpa using hm
        omega
      subst hm0
      simp only [mapMaskP]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i, hi, _, _⟩)
        · exact h
        · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro m acc hm
      rw [mapMaskP_succ]
      by_cases hm0 : m = 0
      · subst hm0
        rw [Nat.beq_refl]
        simp only [Bool.cond_true]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨i, hi, hbit, _⟩)
          · exact h
          · rw [Nat.zero_testBit] at hbit; exact Bool.noConfusion hbit
      · have hbeq : Nat.beq m 0 = false := by
          cases h : Nat.beq m 0 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true h) hm0
        rw [hbeq]
        simp only [Bool.cond_false]
        have ht_bit : m.testBit (Nat.log2 m) = true := Nat.testBit_log2 hm0
        have ht_lt : Nat.log2 m < n + 1 := log2_lt_of_lt m hm0 hm
        have ht_le : Nat.log2 m ≤ n := Nat.lt_succ_iff.mp ht_lt
        have hm'_lt : Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m)) < 2 ^ n :=
          Nat.lt_of_lt_of_le
            (xor_pow_two_lt m (Nat.log2 m) ht_bit (fun i hi => testBit_log2_gt m hm0 hi))
            (Nat.pow_le_pow_of_le (by decide : 1 < 2) ht_le)
        have hper : Nat.land (Nat.shiftRight P (Nat.mul 7 (Nat.log2 m))) 127
            = permAt P (Nat.log2 m) := rfl
        have hacc' : (Nat.lor acc (Nat.shiftLeft 1
              (Nat.land (Nat.shiftRight P (Nat.mul 7 (Nat.log2 m))) 127))).testBit j
            = (acc.testBit j || decide (j = permAt P (Nat.log2 m))) := by
          rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', testBit_shiftLeft_one, hper]
        have hmask_bit (i : Nat) : (Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m))).testBit i
            = (m.testBit i && decide (i ≠ Nat.log2 m)) := by
          rw [Nat.xor_eq, Nat.shiftLeft_eq']
          exact testBit_xor_pow_two m (Nat.log2 m) ht_bit i
        have ih' := ih (Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m)))
          (Nat.lor acc (Nat.shiftLeft 1
            (Nat.land (Nat.shiftRight P (Nat.mul 7 (Nat.log2 m))) 127))) hm'_lt
        rw [ih', hacc', Bool.or_eq_true_iff]
        constructor
        · rintro ((hacc | hperm) | ⟨i, hi, hbi, hpi⟩)
          · exact Or.inl hacc
          · exact Or.inr ⟨Nat.log2 m, ht_lt, ht_bit, (of_decide_eq_true hperm).symm⟩
          · have hbi' : m.testBit i = true := by
              have h' : (m.testBit i && decide (i ≠ Nat.log2 m)) = true := by
                rw [← hmask_bit i]; exact hbi
              exact (Bool.and_eq_true_iff.mp h').1
            exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hbi', hpi⟩
        · rintro (hacc | ⟨i, hi, hbi, hpi⟩)
          · exact Or.inl (Or.inl hacc)
          · by_cases hit : i = Nat.log2 m
            · subst hit
              exact Or.inl (Or.inr (decide_eq_true_eq.mpr hpi.symm))
            · have hlt : i < Nat.log2 m := by
                rcases Nat.lt_or_gt_of_ne hit with h | h
                · exact h
                · exfalso
                  have hf : m.testBit i = false := testBit_log2_gt m hm0 h
                  rw [hbi] at hf
                  exact Bool.noConfusion hf
              have hbi' : (Nat.xor m (Nat.shiftLeft 1 (Nat.log2 m))).testBit i = true := by
                rw [hmask_bit i, hbi, decide_eq_true_eq.mpr hit, Bool.and_true]
              exact Or.inr ⟨i, by omega, hbi', hpi⟩

theorem testBit_mapMaskP (P n m acc j : Nat) (hm : m < 2 ^ n) :
    (mapMaskP P n m acc).testBit j = true ↔
      acc.testBit j = true ∨ ∃ i, i < n ∧ m.testBit i = true ∧ permAt P i = j :=
  testBit_mapMaskP_aux P j n m acc hm

private lemma filter_cons_length (p : Nat → Bool) (k : Nat) (l : List Nat) :
    ((k :: l).filter p).length = (p k).toNat + (l.filter p).length := by
  rw [List.filter_cons]
  by_cases hp : p k = true
  · rw [if_pos hp, List.length_cons, hp, Bool.toNat_true]; omega
  · have hp' : p k = false := by
      cases h : p k with
      | false => rfl
      | true => exact absurd h hp
    rw [if_neg hp, hp', Bool.toNat_false]; omega

private lemma shiftRight_land_one (m k : Nat) : (m >>> k) &&& 1 = (m.testBit k).toNat := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> simp [h]

private lemma foldl_popc (m : Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun a k => a + ((m >>> k) &&& 1)) a
      = a + (l.filter (fun k => m.testBit k)).length := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih =>
      rw [List.foldl_cons, ih (a + ((m >>> k) &&& 1)), shiftRight_land_one, filter_cons_length]
      omega

private lemma decide_eq_self (b : Bool) : decide (b = true) = b := by cases b <;> rfl

theorem popc_eq (m : Nat) :
    popc m = ((List.range 72).filter fun k => m.testBit k = true).length := by
  change (List.range 72).foldl (fun a k => a + ((m >>> k) &&& 1)) 0
      = ((List.range 72).filter fun k => m.testBit k = true).length
  rw [foldl_popc, Nat.zero_add]
  exact congrArg List.length
    (List.filter_congr (l := List.range 72) fun k _ => (decide_eq_self (m.testBit k)).symm)

theorem hasFive_iff (R : Nat) (l : List Nat) (c : Nat) :
    hasFive R l c = true ↔ 5 ≤ c + (l.filter fun m => Nat.land R m == R).length := by
  induction l generalizing c with
  | nil =>
      rw [hasFive_nil]
      simp only [List.filter_nil, List.length_nil, Nat.add_zero, Nat.ble_eq]
  | cons m ms ih =>
      rw [hasFive_cons]
      by_cases h5 : 5 ≤ c
      · rw [Nat.ble_eq.mpr h5]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        omega
      · have hb : Nat.ble 5 c = false := by
          cases h : Nat.ble 5 c with
          | false => rfl
          | true => exact absurd (Nat.ble_eq.mp h) h5
        rw [hb]
        simp only [Bool.cond_false]
        by_cases hpm : Nat.beq (Nat.land R m) R = true
        · have hpmf : (Nat.land R m == R) = true := hpm
          have ih' := ih (bif Nat.beq (Nat.land R m) R then c + 1 else c)
          simp only [hpm, Bool.cond_true] at ih' ⊢
          rw [List.filter_cons, if_pos hpmf, List.length_cons, ih']
          omega
        · have hpm' : Nat.beq (Nat.land R m) R = false := by
            cases h : Nat.beq (Nat.land R m) R with
            | false => rfl
            | true => exact absurd h hpm
          have hpmf' : (Nat.land R m == R) = false := hpm'
          have ih' := ih (bif Nat.beq (Nat.land R m) R then c + 1 else c)
          simp only [hpm', Bool.cond_false] at ih' ⊢
          rw [List.filter_cons, if_neg (by rw [hpmf']; exact fun h => Bool.noConfusion h), ih']

private lemma rowsOK_aux (S : Nat) :
    ∀ n rem, rem < 2 ^ 72 → rowsOK S n rem = true → ∀ k, rem.testBit k = true →
      ∃ k0, rem.testBit k0 = true ∧ Reach adjLit S k0 k ∧
        rowOK S (compOf adjLit S k0) = true := by
  intro n
  induction n with
  | zero =>
      intro rem _ hrows k hk
      have h0 : rem = 0 := Nat.eq_of_beq_eq_true hrows
      rw [h0, Nat.zero_testBit] at hk
      exact Bool.noConfusion hk
  | succ n ih =>
      intro rem hrem hrows k hk
      rw [rowsOK_succ] at hrows
      by_cases hrem0 : rem = 0
      · subst hrem0
        rw [Nat.zero_testBit] at hk
        exact Bool.noConfusion hk
      · have hbeq : Nat.beq rem 0 = false := by
          cases h : Nat.beq rem 0 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true h) hrem0
        rw [hbeq] at hrows
        simp only [Bool.cond_false] at hrows
        obtain ⟨hrow, hrows'⟩ := Bool.and_eq_true_iff.mp hrows
        have hk72 : k < 72 := by
          by_contra hge
          have hle : 72 ≤ k := Nat.le_of_not_lt hge
          have hf : rem.testBit k = false := (lt_two_pow_iff_testBit rem 72).mp hrem k hle
          rw [hf] at hk
          exact Bool.noConfusion hk
        have hk1_lt : Nat.log2 rem < 72 := log2_lt_of_lt rem hrem0 hrem
        have hk1_bit : rem.testBit (Nat.log2 rem) = true := Nat.testBit_log2 hrem0
        by_cases hck : (compOf adjLit S (Nat.log2 rem)).testBit k = true
        · exact ⟨Nat.log2 rem, hk1_bit,
            compOf_sound adjLit S (Nat.log2 rem) hk1_lt hck, hrow⟩
        · have hck' : (compOf adjLit S (Nat.log2 rem)).testBit k = false := by
            cases h : (compOf adjLit S (Nat.log2 rem)).testBit k with
            | false => rfl
            | true => exact absurd h hck
          have hrem'_bit : (Nat.land rem (Nat.xor (compOf adjLit S (Nat.log2 rem)) M72)).testBit k
              = true := by
            rw [Nat.land_eq, Nat.testBit_and, hk, Nat.xor_eq, Nat.testBit_xor, hck', M72_testBit,
                decide_eq_true_eq.mpr hk72]
            rfl
          have hrem'_lt : (Nat.land rem (Nat.xor (compOf adjLit S (Nat.log2 rem)) M72)) < 2 ^ 72 := by
            rw [Nat.land_eq]
            exact Nat.lt_of_le_of_lt Nat.and_le_left hrem
          obtain ⟨k0, hk0, hreach, hrowk0⟩ :=
            ih (Nat.land rem (Nat.xor (compOf adjLit S (Nat.log2 rem)) M72)) hrem'_lt hrows'
              k hrem'_bit
          refine ⟨k0, ?_, hreach, hrowk0⟩
          rw [Nat.land_eq, Nat.testBit_and] at hk0
          exact (Bool.and_eq_true_iff.mp hk0).1

theorem rowsOK_spec (S n rem : Nat) (h : rowsOK S n rem = true) (hrem : rem < 2 ^ 72) {k : Nat}
    (hk : rem.testBit k = true) :
    ∃ k0, rem.testBit k0 = true ∧ Reach adjLit S k0 k ∧
      rowOK S (compOf adjLit S k0) = true :=
  rowsOK_aux S n rem hrem h k hk

theorem tableOK_spec {S : Nat} (hS : S ∈ sigsLit) (hS72 : S < 2 ^ 72) {k : Nat}
    (hk : S.testBit k = true) :
    ∃ k0, S.testBit k0 = true ∧ Reach adjLit S k0 k ∧ rowOK S (compOf adjLit S k0) = true := by
  have h := e6FourTable_ok
  change sigsLit.all vecOK = true at h
  have hvec : vecOK S = true := (List.all_eq_true.mp h) S hS
  have hrows : rowsOK S 72 S = true := by simpa only [vecOK] using hvec
  exact rowsOK_spec S 72 S hrows hS72 hk

end CFSG.Assembly.E6FourCentChk

end
