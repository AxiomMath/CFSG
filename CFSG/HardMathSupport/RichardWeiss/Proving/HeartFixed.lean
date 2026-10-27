module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {n : ℕ}

theorem exists_ne_pair_heart (hn : 3 ≤ n) (a b : Fin n) :
    ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := by
    intro e _
    by_cases h1 : e = a
    · simp [h1]
    · simp [h e h1]
  have h4 := Finset.card_le_card hsub
  have h5 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  simp at h4
  omega

theorem pairEW_ne_zero_altHeart (hn : 3 ≤ n) {a j : Fin n} (haj : a ≠ j) :
    (pairEW a j : altHeart n) ≠ 0 := by
  obtain ⟨c, hca, hcj⟩ := exists_ne_pair_heart hn a j
  exact mk_pairEW_ne_zero haj hca hcj

theorem altHeart_fixed_form (hn : 6 ≤ n) (hev : Even n) (a j : Fin n) (haj : a ≠ j)
    (x : altHeart n)
    (hfix : ∀ σ : Perm (Fin n), σ.IsThreeCycle → (∀ y, σ y ≠ y → y ≠ a ∧ y ≠ j) →
        altAct σ x = x) :
    x = 0 ∨ x = (pairEW a j : altHeart n) := by
  obtain ⟨xv, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hinv : ∀ σ : Perm (Fin n), σ.IsThreeCycle → σ a = a → σ j = j →
      ∀ i, (xv : Fin n → ZMod 2) (σ i) = (xv : Fin n → ZMod 2) i := by
    intro σ hσ ha hj i
    have hyσ : (evenWeightPerm σ xv : altHeart n) = (xv : altHeart n) := by
      rw [← altAct_mk]
      apply hfix σ hσ
      intro y hy
      constructor
      · rintro rfl; exact hy ha
      · rintro rfl; exact hy hj
    have := apply_inv_eq_of_mk_eq ha hyσ (σ i)
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
    exact this.symm
  obtain ⟨p0, hp0a, hp0j⟩ := exists_ne_pair_heart (by omega : 3 ≤ n) a j
  have hconst : ∀ p q : Fin n, p ≠ a → p ≠ j → q ≠ a → q ≠ j →
      (xv : Fin n → ZMod 2) p = (xv : Fin n → ZMod 2) q := by
    intro p q hpa hpj hqa hqj
    by_cases hpq : p = q
    · rw [hpq]
    obtain ⟨r, hra, hrj, hrp, hrq⟩ := exists_ne_four (by omega : 5 ≤ n) a j p q
    have hqp : q ≠ p := fun h => hpq h.symm
    have hqr : q ≠ r := Ne.symm hrq
    have hpr : p ≠ r := Ne.symm hrp
    have hσ : (swap q p * swap q r).IsThreeCycle := by
      apply isThreeCycle_swap_mul_swap_same <;> assumption
    have hσp : (swap q p * swap q r) p = q := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpq (Ne.symm hrp), swap_apply_right]
    have hσa : (swap q p * swap q r) a = a := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hqa) (Ne.symm hra),
        swap_apply_of_ne_of_ne (Ne.symm hqa) (Ne.symm hpa)]
    have hσj : (swap q p * swap q r) j = j := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hqj) (Ne.symm hrj),
        swap_apply_of_ne_of_ne (Ne.symm hqj) (Ne.symm hpj)]
    have := hinv _ hσ hσa hσj p
    rw [hσp] at this
    exact this.symm
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, ∀ p, p ≠ a → p ≠ j → (xv : Fin n → ZMod 2) p = c :=
    ⟨_, fun p hpa hpj => hconst p p0 hpa hpj hp0a hp0j⟩
  have hsum : ∑ i, (xv : Fin n → ZMod 2) i = 0 := xv.2
  have hcard : ((Finset.univ.erase a).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm haj, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  have hcast : ((n - 2 : ℕ) : ZMod 2) = 0 := by
    obtain ⟨k, rfl⟩ := hev
    rw [show k + k - 2 = (k - 1) + (k - 1) by omega]
    push_cast
    exact (show ∀ c : ZMod 2, c + c = 0 by decide) _
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase j, (xv : Fin n → ZMod 2) i = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
      exact hc i hi.2 hi.1), Finset.sum_const, hcard, nsmul_eq_mul, hcast, zero_mul]
  have h1 : (xv : Fin n → ZMod 2) a + ∑ i ∈ Finset.univ.erase a, (xv : Fin n → ZMod 2) i =
      ∑ i, (xv : Fin n → ZMod 2) i :=
    Finset.add_sum_erase _ _ (Finset.mem_univ a)
  have h2 : (xv : Fin n → ZMod 2) j + ∑ i ∈ (Finset.univ.erase a).erase j, (xv : Fin n → ZMod 2) i =
      ∑ i ∈ Finset.univ.erase a, (xv : Fin n → ZMod 2) i :=
    Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm haj, Finset.mem_univ j⟩)
  have hab : (xv : Fin n → ZMod 2) a + (xv : Fin n → ZMod 2) j = 0 := by
    rw [← h2, hrest, add_zero] at h1
    rw [hsum] at h1
    exact h1
  have hZ2 : ∀ u v : ZMod 2, u + v = 0 → u = v := by decide
  have hab' : (xv : Fin n → ZMod 2) a = (xv : Fin n → ZMod 2) j := hZ2 _ _ hab
  have hZ3 : ∀ u v : ZMod 2, u ≠ v → u = v + 1 := by decide
  have hZ4 : ∀ v : ZMod 2, -(v + 1) + (1 + 0) = v := by decide
  have hZ5 : ∀ v : ZMod 2, -(v + 1) + (0 + 1) = v := by decide
  have hZ6 : ∀ v : ZMod 2, -v + (0 + 0) = v := by decide
  by_cases hca : (xv : Fin n → ZMod 2) a = c
  · left
    apply (QuotientAddGroup.eq_zero_iff _).2
    apply mem_evenWeightOnes_of_forall_eq (c := c)
    intro i
    by_cases hia : i = a
    · rw [hia]; exact hca
    by_cases hij : i = j
    · rw [hij, ← hab']; exact hca
    exact hc i hia hij
  · right
    apply QuotientAddGroup.eq.2
    apply mem_evenWeightOnes_of_forall_eq (c := c)
    have hea : (xv : Fin n → ZMod 2) a = c + 1 := hZ3 _ _ hca
    have hej : (xv : Fin n → ZMod 2) j = c + 1 := by rw [← hab']; exact hea
    intro i
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply, pairEW_apply]
    by_cases hia : i = a
    · rw [hia, ite_eq_left (rfl : a = a), ite_eq_right haj, hea]
      exact hZ4 c
    by_cases hij : i = j
    · rw [hij, ite_eq_right (Ne.symm haj), ite_eq_left (rfl : j = j), hej]
      exact hZ5 c
    rw [ite_eq_right hia, ite_eq_right hij, hc i hia hij]
    exact hZ6 c

end CFSG.HardMathSupport.RichardWeiss.Proving
