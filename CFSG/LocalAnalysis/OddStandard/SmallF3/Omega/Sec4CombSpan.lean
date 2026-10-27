module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped CharTwo

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private def evec (i : Fin 7) : Fin 7 → ZMod 2 :=
  Pi.single i 1

private lemma sum_evec_eq (s : Finset (Fin 7)) :
    (∑ x ∈ s, evec x) = fun a => if a ∈ s then (1 : ZMod 2) else 0 := by
  funext a; rw [Finset.sum_apply]
  exact Finset.sum_pi_single a (fun _ => (1 : ZMod 2)) s

private lemma isEvenVec_sum_evec {s : Finset (Fin 7)} (h : Even s.card) :
    IsEvenVec (∑ x ∈ s, evec x) := by
  rw [sum_evec_eq]
  unfold IsEvenVec
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact ZMod.natCast_eq_zero_iff_even.mpr h

private lemma vecWeight_sum_evec (s : Finset (Fin 7)) :
    vecWeight (∑ x ∈ s, evec x) = s.card := by
  have hf : (Finset.univ.filter fun a => (if a ∈ s then (1 : ZMod 2) else 0) ≠ 0) = s := by
    rw [show (Finset.univ.filter fun a => (if a ∈ s then (1 : ZMod 2) else 0) ≠ 0)
        = Finset.univ.filter (fun a => a ∈ s) by
      apply Finset.filter_congr
      intro a _; by_cases ha : a ∈ s <;> simp [ha]]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold vecWeight
  rw [sum_evec_eq, hf]

private lemma evec_add_evec_eq_sum {i j : Fin 7} (hij : i ≠ j) :
    evec i + evec j = ∑ x ∈ ({i, j} : Finset (Fin 7)), evec x := by
  rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]

private lemma isEvenVec_evec_add {i j : Fin 7} (hij : i ≠ j) : IsEvenVec (evec i + evec j) := by
  rw [evec_add_evec_eq_sum hij]
  exact isEvenVec_sum_evec (by
    rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]; exact ⟨1, rfl⟩)

private lemma vecWeight_evec_add {i j : Fin 7} (hij : i ≠ j) :
    vecWeight (evec i + evec j) = 2 := by
  rw [evec_add_evec_eq_sum hij, vecWeight_sum_evec,
    Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]

private lemma charTwo_add_add_cancel (a b c : Fin 7 → ZMod 2) :
    (a + c) + (b + c) = a + b := by
  rw [add_comm b c, add_assoc a c (c + b), CharTwo.add_cancel_left]

private lemma charTwo_add_add_self (a b : Fin 7 → ZMod 2) : a + (b + a) = b := by
  rw [add_comm b a, CharTwo.add_cancel_left]

private lemma evec_add_evec_mem_closure (k : ℕ) (hk : k = 4 ∨ k = 6) {i j : Fin 7}
    (hij : i ≠ j) :
    evec i + evec j ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧ vecWeight u = k} := by
  have hkE : Even k := by rcases hk with rfl | rfl <;> decide
  have hkle : k - 1 ≤ (({i, j} : Finset (Fin 7))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton,
      Fintype.card_fin]
    rcases hk with rfl | rfl <;> norm_num
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hkle
  have hi_t : i ∉ t := fun hit => by simpa using ht_sub hit
  have hj_t : j ∉ t := fun hjt => by simpa using ht_sub hjt
  have hci : (insert i t).card = k := by
    rw [Finset.card_insert_of_notMem hi_t, ht_card]; rcases hk with rfl | rfl <;> norm_num
  have hcj : (insert j t).card = k := by
    rw [Finset.card_insert_of_notMem hj_t, ht_card]; rcases hk with rfl | rfl <;> norm_num
  have gen : ∀ x, x = i ∨ x = j → (∑ y ∈ insert x t, evec y) ∈
      AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧ vecWeight u = k} := by
    rintro x (rfl | rfl)
    · exact AddSubgroup.subset_closure ⟨isEvenVec_sum_evec (by rw [hci]; exact hkE),
        by rw [vecWeight_sum_evec, hci]⟩
    · exact AddSubgroup.subset_closure ⟨isEvenVec_sum_evec (by rw [hcj]; exact hkE),
        by rw [vecWeight_sum_evec, hcj]⟩
  have hsum_i : (∑ y ∈ insert i t, evec y) = evec i + ∑ y ∈ t, evec y := Finset.sum_insert hi_t
  have hsum_j : (∑ y ∈ insert j t, evec y) = evec j + ∑ y ∈ t, evec y := Finset.sum_insert hj_t
  have hidentity : evec i + evec j =
      (∑ y ∈ insert i t, evec y) + (∑ y ∈ insert j t, evec y) := by
    rw [hsum_i, hsum_j]
    exact (charTwo_add_add_cancel (evec i) (evec j) (∑ y ∈ t, evec y)).symm
  rw [hidentity]
  exact AddSubgroup.add_mem _ (gen i (Or.inl rfl)) (gen j (Or.inr rfl))

private lemma exists_two_support {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hv0 : v ≠ 0) :
    ∃ i j : Fin 7, i ≠ j ∧ v i ≠ 0 ∧ v j ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h
    exact hv0 (funext fun i => by simpa using h i)
  by_contra h
  push Not at h
  have hsum : (∑ k, v k) = v i := by
    rw [Finset.sum_eq_single i]
    · intro b _ hb; exact h i b (Ne.symm hb) hi
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  change (∑ k, v k) = 0 at hv
  rw [hsum] at hv
  exact hi hv

private lemma evenVec_mem_of_evec_add {B : AddSubgroup (Fin 7 → ZMod 2)}
    (hB : ∀ i j : Fin 7, i ≠ j → evec i + evec j ∈ B) :
    ∀ v : Fin 7 → ZMod 2, IsEvenVec v → v ∈ B := by
  intro v hv
  have key : ∀ (n : ℕ) (v : Fin 7 → ZMod 2), IsEvenVec v → vecWeight v = n → v ∈ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hw
      by_cases hv0 : v = 0
      · subst hv0
        exact B.zero_mem
      · obtain ⟨i, j, hij, hi, hj⟩ := exists_two_support hv hv0
        have hXeven : IsEvenVec (evec i + evec j) := isEvenVec_evec_add hij
        have hu_even : IsEvenVec (v + (evec i + evec j)) := isEvenVec_add hv hXeven
        have hlt : vecWeight (v + (evec i + evec j)) < vecWeight v := by
          have hsub : (Finset.univ.filter fun k => (v + (evec i + evec j)) k ≠ 0) ⊆
              (Finset.univ.filter fun k => v k ≠ 0).erase i := by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            have hki : k ≠ i := by
              rintro rfl
              exact hk (by simp [Pi.add_apply, evec, Pi.single_eq_same,
                zmod2_eq_one_of_ne_zero hi, Pi.single_eq_of_ne hij])
            have hkj : k ≠ j := by
              rintro rfl
              exact hk (by simp [Pi.add_apply, evec, Pi.single_eq_same,
                zmod2_eq_one_of_ne_zero hj, Pi.single_eq_of_ne (Ne.symm hij)])
            exact ⟨hki, by simpa only [Pi.add_apply, evec, Pi.single_eq_of_ne hki,
              Pi.single_eq_of_ne hkj, add_zero] using hk⟩
          have hcard : vecWeight (v + (evec i + evec j)) ≤ vecWeight v - 1 := by
            unfold vecWeight
            calc (Finset.univ.filter fun k => (v + (evec i + evec j)) k ≠ 0).card
                ≤ ((Finset.univ.filter fun k => v k ≠ 0).erase i).card := Finset.card_le_card hsub
              _ = (Finset.univ.filter fun k => v k ≠ 0).card - 1 :=
                  Finset.card_erase_of_mem (by simp [hi])
          have hpos : 0 < vecWeight v := by
            unfold vecWeight
            exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
          omega
        have hu_mem : v + (evec i + evec j) ∈ B :=
          ih (vecWeight (v + (evec i + evec j))) (by rw [← hw]; exact hlt)
            (v + (evec i + evec j)) hu_even rfl
        have hgen : evec i + evec j ∈ B := hB i j hij
        have hgoal : v = (evec i + evec j) + (v + (evec i + evec j)) :=
          (charTwo_add_add_self (evec i + evec j) v).symm
        rw [hgoal]
        exact B.add_mem hgen hu_mem
  exact key (vecWeight v) v hv rfl

theorem isEvenVec_mem_closure_weight {k : ℕ} (hk : k = 2 ∨ k = 4 ∨ k = 6)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    v ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧ vecWeight u = k} := by
  rcases hk with rfl | hk
  · exact evenVec_mem_of_evec_add
      (fun i j hij => AddSubgroup.subset_closure
        (show IsEvenVec (evec i + evec j) ∧ vecWeight (evec i + evec j) = 2 from
          ⟨isEvenVec_evec_add hij, vecWeight_evec_add hij⟩))
      v hv
  rcases hk with rfl | rfl
  · exact evenVec_mem_of_evec_add (fun i j hij => evec_add_evec_mem_closure 4 (Or.inl rfl) hij) v hv
  · exact evenVec_mem_of_evec_add (fun i j hij => evec_add_evec_mem_closure 6 (Or.inr rfl) hij) v hv

end CFSG.OddStandard.SmallF3.Omega
