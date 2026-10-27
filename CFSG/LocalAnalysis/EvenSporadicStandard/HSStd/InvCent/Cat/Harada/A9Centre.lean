module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

private lemma sign_two (a b k l : Fin 9) (hab : a ≠ b) (hkl : k ≠ l) :
    Equiv.Perm.sign (Equiv.swap a b * Equiv.swap k l) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hkl]
  decide

private lemma sign_three (a b e : Fin 9) (hab : a ≠ b) (hbe : b ≠ e) :
    Equiv.Perm.sign (Equiv.swap a b * Equiv.swap b e) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbe]
  decide

private lemma moved_of_comm {z c : Equiv.Perm (Fin 9)} (h : c * z = z * c) {i : Fin 9}
    (hi : c i ≠ i) : c (z i) ≠ z i := by
  have h' : c (z i) = z (c i) := Equiv.Perm.congr_fun h i
  rw [h']
  exact fun hh => hi (z.injective hh)

private lemma z_mem_support_of_comm {z c : Equiv.Perm (Fin 9)} (h : c * z = z * c)
    {i : Fin 9} (hi : c i ≠ i) : z i ∈ c.support :=
  Equiv.Perm.mem_support.mpr (moved_of_comm h hi)

private lemma mem_triple_of_comm {z : Equiv.Perm (Fin 9)} {k a b : Fin 9}
    (h : (Equiv.swap k a * Equiv.swap a b) * z = z * (Equiv.swap k a * Equiv.swap a b))
    (hn : List.Nodup [k, a, b]) : z k ∈ ({k, a, b} : Finset (Fin 9)) := by
  have hk : (Equiv.swap k a * Equiv.swap a b) k ≠ k := by
    rw [← Equiv.Perm.mem_support, Equiv.Perm.support_swap_mul_swap hn]
    simp
  have hm := z_mem_support_of_comm h hk
  rwa [Equiv.Perm.support_swap_mul_swap hn] at hm

private lemma eq_left_of_mem_triples {x k a b c d : Fin 9}
    (h1 : x = k ∨ x = a ∨ x = b) (h2 : x = k ∨ x = c ∨ x = d)
    (hak : a ≠ k) (hbk : b ≠ k) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : x = k := by
  rcases h1 with h1 | h1 | h1
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hak
    · exact absurd (h1.symm.trans h2) hac
    · exact absurd (h1.symm.trans h2) had
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hbk
    · exact absurd (h1.symm.trans h2) hbc
    · exact absurd (h1.symm.trans h2) hbd

private lemma mem_pair_of_comm {z : Equiv.Perm (Fin 9)} {p q k l i : Fin 9}
    (hpq : p ≠ q) (hpk : p ≠ k) (hpl : p ≠ l) (hqk : q ≠ k) (hql : q ≠ l)
    (h : (Equiv.swap p q * Equiv.swap k l) * z = z * (Equiv.swap p q * Equiv.swap k l))
    (hk : z k = k) (hl : z l = l) (hip : i = p ∨ i = q) : z i = p ∨ z i = q := by
  have hsubset : (Equiv.swap p q * Equiv.swap k l).support ⊆
      ({p, q, k, l} : Finset (Fin 9)) := by
    intro x hx
    by_contra hx'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
    have hfix : (Equiv.swap p q * Equiv.swap k l) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx'.2.2.1 hx'.2.2.2,
        Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2.1]
    exact (Equiv.Perm.mem_support.mp hx) hfix
  have hci : (Equiv.swap p q * Equiv.swap k l) i ≠ i := by
    rcases hip with rfl | rfl
    · intro hh
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpk hpl,
        Equiv.swap_apply_left] at hh
      exact hpq hh.symm
    · intro hh
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hqk hql,
        Equiv.swap_apply_right] at hh
      exact hpq hh
  have hmem : z i ∈ ({p, q, k, l} : Finset (Fin 9)) :=
    hsubset (z_mem_support_of_comm h hci)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · exact Or.inl hmem
  · exact Or.inr hmem
  · exact absurd (z.injective (hmem.trans hk.symm)) (by
      rcases hip with rfl | rfl
      · exact hpk
      · exact hqk)
  · exact absurd (z.injective (hmem.trans hl.symm)) (by
      rcases hip with rfl | rfl
      · exact hpl
      · exact hql)

theorem a9_centre_aux (z : Equiv.Perm (Fin 9)) (hz : Equiv.Perm.sign z = 1)
    (hcomm : ∀ c : Equiv.Perm (Fin 9), Equiv.Perm.sign c = 1 →
      c * (Equiv.swap 0 1 * Equiv.swap 2 3) =
        (Equiv.swap 0 1 * Equiv.swap 2 3) * c → c * z = z * c) :
    z = 1 ∨ z = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  have h4 : z 4 = 4 := by
    have h1 : z 4 ∈ ({4, 5, 6} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 4) (a := 5) (b := 6)
        (hcomm (c := Equiv.swap 4 5 * Equiv.swap 5 6)
          (sign_three 4 5 6 (by decide) (by decide)) (by decide)) (by decide)
    have h2 : z 4 ∈ ({4, 7, 8} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 4) (a := 7) (b := 8)
        (hcomm (c := Equiv.swap 4 7 * Equiv.swap 7 8)
          (sign_three 4 7 8 (by decide) (by decide)) (by decide)) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact eq_left_of_mem_triples h1 h2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5 : z 5 = 5 := by
    have h1 : z 5 ∈ ({5, 4, 6} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 5) (a := 4) (b := 6)
        (hcomm (c := Equiv.swap 5 4 * Equiv.swap 4 6)
          (sign_three 5 4 6 (by decide) (by decide)) (by decide)) (by decide)
    have h2 : z 5 ∈ ({5, 7, 8} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 5) (a := 7) (b := 8)
        (hcomm (c := Equiv.swap 5 7 * Equiv.swap 7 8)
          (sign_three 5 7 8 (by decide) (by decide)) (by decide)) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact eq_left_of_mem_triples h1 h2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h6 : z 6 = 6 := by
    have h1 : z 6 ∈ ({6, 4, 5} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 6) (a := 4) (b := 5)
        (hcomm (c := Equiv.swap 6 4 * Equiv.swap 4 5)
          (sign_three 6 4 5 (by decide) (by decide)) (by decide)) (by decide)
    have h2 : z 6 ∈ ({6, 7, 8} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 6) (a := 7) (b := 8)
        (hcomm (c := Equiv.swap 6 7 * Equiv.swap 7 8)
          (sign_three 6 7 8 (by decide) (by decide)) (by decide)) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact eq_left_of_mem_triples h1 h2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h7 : z 7 = 7 := by
    have h1 : z 7 ∈ ({7, 4, 5} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 7) (a := 4) (b := 5)
        (hcomm (c := Equiv.swap 7 4 * Equiv.swap 4 5)
          (sign_three 7 4 5 (by decide) (by decide)) (by decide)) (by decide)
    have h2 : z 7 ∈ ({7, 6, 8} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 7) (a := 6) (b := 8)
        (hcomm (c := Equiv.swap 7 6 * Equiv.swap 6 8)
          (sign_three 7 6 8 (by decide) (by decide)) (by decide)) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact eq_left_of_mem_triples h1 h2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h8 : z 8 = 8 := by
    have h1 : z 8 ∈ ({8, 4, 5} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 8) (a := 4) (b := 5)
        (hcomm (c := Equiv.swap 8 4 * Equiv.swap 4 5)
          (sign_three 8 4 5 (by decide) (by decide)) (by decide)) (by decide)
    have h2 : z 8 ∈ ({8, 6, 7} : Finset (Fin 9)) :=
      mem_triple_of_comm (k := 8) (a := 6) (b := 7)
        (hcomm (c := Equiv.swap 8 6 * Equiv.swap 6 7)
          (sign_three 8 6 7 (by decide) (by decide)) (by decide)) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact eq_left_of_mem_triples h1 h2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hz0 : z 0 = 0 ∨ z 0 = 1 :=
    mem_pair_of_comm (p := 0) (q := 1) (k := 4) (l := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hcomm (c := Equiv.swap 0 1 * Equiv.swap 4 5)
        (sign_two 0 1 4 5 (by decide) (by decide)) (by decide)) h4 h5 (Or.inl rfl)
  have hz1 : z 1 = 0 ∨ z 1 = 1 :=
    mem_pair_of_comm (p := 0) (q := 1) (k := 4) (l := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hcomm (c := Equiv.swap 0 1 * Equiv.swap 4 5)
        (sign_two 0 1 4 5 (by decide) (by decide)) (by decide)) h4 h5 (Or.inr rfl)
  have hz2 : z 2 = 2 ∨ z 2 = 3 :=
    mem_pair_of_comm (p := 2) (q := 3) (k := 4) (l := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hcomm (c := Equiv.swap 2 3 * Equiv.swap 4 5)
        (sign_two 2 3 4 5 (by decide) (by decide)) (by decide)) h4 h5 (Or.inl rfl)
  have hz3 : z 3 = 2 ∨ z 3 = 3 :=
    mem_pair_of_comm (p := 2) (q := 3) (k := 4) (l := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (hcomm (c := Equiv.swap 2 3 * Equiv.swap 4 5)
        (sign_two 2 3 4 5 (by decide) (by decide)) (by decide)) h4 h5 (Or.inr rfl)
  have h01 : (z 0 = 0 ∧ z 1 = 1) ∨ (z 0 = 1 ∧ z 1 = 0) := by
    rcases hz0 with h0 | h0 <;> rcases hz1 with h1 | h1
    · exact absurd (z.injective (h0.trans h1.symm)) (by decide)
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (z.injective (h0.trans h1.symm)) (by decide)
  have h23 : (z 2 = 2 ∧ z 3 = 3) ∨ (z 2 = 3 ∧ z 3 = 2) := by
    rcases hz2 with h2 | h2 <;> rcases hz3 with h3 | h3
    · exact absurd (z.injective (h2.trans h3.symm)) (by decide)
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h2, h3⟩
    · exact absurd (z.injective (h2.trans h3.symm)) (by decide)
  rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases h23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
    · exact h4.trans (by decide)
    · exact h5.trans (by decide)
    · exact h6.trans (by decide)
    · exact h7.trans (by decide)
    · exact h8.trans (by decide)
  · exfalso
    have hz' : z = Equiv.swap 2 3 := by
      apply Equiv.ext
      intro i
      fin_cases i
      · exact h0.trans (by decide)
      · exact h1.trans (by decide)
      · exact h2.trans (by decide)
      · exact h3.trans (by decide)
      · exact h4.trans (by decide)
      · exact h5.trans (by decide)
      · exact h6.trans (by decide)
      · exact h7.trans (by decide)
      · exact h8.trans (by decide)
    rw [hz', Equiv.Perm.sign_swap (by decide)] at hz
    exact absurd hz (by decide)
  · exfalso
    have hz' : z = Equiv.swap 0 1 := by
      apply Equiv.ext
      intro i
      fin_cases i
      · exact h0.trans (by decide)
      · exact h1.trans (by decide)
      · exact h2.trans (by decide)
      · exact h3.trans (by decide)
      · exact h4.trans (by decide)
      · exact h5.trans (by decide)
      · exact h6.trans (by decide)
      · exact h7.trans (by decide)
      · exact h8.trans (by decide)
    rw [hz', Equiv.Perm.sign_swap (by decide)] at hz
    exact absurd hz (by decide)
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
    · exact h4.trans (by decide)
    · exact h5.trans (by decide)
    · exact h6.trans (by decide)
    · exact h7.trans (by decide)
    · exact h8.trans (by decide)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
