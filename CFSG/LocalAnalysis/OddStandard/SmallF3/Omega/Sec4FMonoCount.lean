module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBSpin

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def sec4FOffCount (a b : Fin 7) (u : Fin 7 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun k => k ≠ a ∧ k ≠ b ∧ u k ≠ 0).card

private def sec4FOffSet (a b : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter fun k => k ≠ a ∧ k ≠ b

private def sec4FPairSet (a b : Fin 7) (v : Fin 7 → ZMod 2) : Finset (Fin 7) :=
  Finset.univ.filter fun i => (i = a ∨ i = b) ∧ v i ≠ 0

private lemma sec4F_zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma sec4FOffSet_card (a b : Fin 7) (hab : a ≠ b) : (sec4FOffSet a b).card = 5 := by
  have h : sec4FOffSet a b = (Finset.univ.erase a).erase b := by
    ext k
    simp only [sec4FOffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a)]
  simp

private lemma sec4FOffCount_eq_filter (a b : Fin 7) (u : Fin 7 → ZMod 2) :
    sec4FOffCount a b u = ((sec4FOffSet a b).filter fun k => u k ≠ 0).card := by
  unfold sec4FOffCount sec4FOffSet
  rw [Finset.filter_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

private lemma sec4FOffCount_eq_zero_imp {a b : Fin 7} {u : Fin 7 → ZMod 2}
    (h : sec4FOffCount a b u = 0) : ∀ k, k ≠ a → k ≠ b → u k = 0 := by
  intro k hka hkb
  by_contra hk
  have hmem : k ∈ Finset.univ.filter (fun k => k ≠ a ∧ k ≠ b ∧ u k ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k, hka, hkb, hk⟩
  have hpos : 0 < (Finset.univ.filter (fun k => k ≠ a ∧ k ≠ b ∧ u k ≠ 0)).card :=
    Finset.card_pos.mpr ⟨k, hmem⟩
  unfold sec4FOffCount at h
  omega

private lemma sec4FOffCount_eq_five_imp {a b : Fin 7} (hab : a ≠ b) {u : Fin 7 → ZMod 2}
    (h : sec4FOffCount a b u = 5) : ∀ k, k ≠ a → k ≠ b → u k ≠ 0 := by
  have hfilter : ((sec4FOffSet a b).filter fun k => u k ≠ 0).card = 5 := by
    rw [← sec4FOffCount_eq_filter]; exact h
  have heq : (sec4FOffSet a b).filter (fun k => u k ≠ 0) = sec4FOffSet a b :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hfilter, sec4FOffSet_card a b hab])
  intro k hka hkb
  have hkS : k ∈ sec4FOffSet a b := by
    rw [sec4FOffSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, hka, hkb⟩
  rw [← heq] at hkS
  exact (Finset.mem_filter.mp hkS).2

private lemma sec4FPairSet_even {a b : Fin 7} (hab : a ≠ b) {v : Fin 7 → ZMod 2}
    (hvab : v a = v b) : Even (sec4FPairSet a b v).card := by
  by_cases hva : v a = 0
  · have h : sec4FPairSet a b v = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [sec4FPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi.1 with hia | hib
      · exact hi.2 (by rw [hia]; exact hva)
      · exact hi.2 (by rw [hib, ← hvab]; exact hva)
    rw [h]; simp
  · have hvb : v b ≠ 0 := by rw [← hvab]; exact hva
    have h : sec4FPairSet a b v = {a, b} := by
      ext i
      simp only [sec4FPairSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hia | hib, _⟩
        · exact Or.inl hia
        · exact Or.inr hib
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hva⟩
        · exact ⟨Or.inr rfl, hvb⟩
    rw [h, Finset.card_pair hab]
    norm_num

private lemma sec4FOffCount_even {a b : Fin 7} (hab : a ≠ b) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hvab : v a = v b) : Even (sec4FOffCount a b v) := by
  have hT : Even (vecWeight v) := (sec4I_isEvenVec_iff_even_vecWeight v).mp hv
  have hP : Even (sec4FPairSet a b v).card := sec4FPairSet_even hab hvab
  have hT_eq : (Finset.univ.filter (fun i => v i ≠ 0))
      = (sec4FOffSet a b).filter (fun k => v k ≠ 0) ∪ sec4FPairSet a b v := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, sec4FOffSet,
      sec4FPairSet]
    constructor
    · intro hvi
      by_cases hia : i = a
      · exact Or.inr ⟨Or.inl hia, hvi⟩
      · by_cases hib : i = b
        · exact Or.inr ⟨Or.inr hib, hvi⟩
        · exact Or.inl ⟨⟨hia, hib⟩, hvi⟩
    · rintro (⟨⟨_, _⟩, hvi⟩ | ⟨_, hvi⟩)
      · exact hvi
      · exact hvi
  have hdisj : Disjoint ((sec4FOffSet a b).filter (fun k => v k ≠ 0)) (sec4FPairSet a b v) := by
    rw [Finset.disjoint_left]
    intro i hi hP
    simp only [Finset.mem_filter, sec4FOffSet, Finset.mem_univ, true_and] at hi
    simp only [sec4FPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    rcases hP.1 with hia | hib
    · exact hi.1.1 hia
    · exact hi.1.2 hib
  have hsum : vecWeight v = sec4FOffCount a b v + (sec4FPairSet a b v).card := by
    unfold vecWeight
    rw [hT_eq, Finset.card_union_of_disjoint hdisj, ← sec4FOffCount_eq_filter]
  rw [hsum] at hT
  exact (Nat.even_add.mp hT).mpr hP

theorem sec4F_mono_count {a b : Fin 7} (hab : a ≠ b) {u v : Fin 7 → ZMod 2} (hv : IsEvenVec v)
    (hvab : v a = v b) (h1 : sec4FOffCount a b u = 0 ∨ sec4FOffCount a b u = 5)
    (h2 : sec4FOffCount a b (u + v) = 0 ∨ sec4FOffCount a b (u + v) = 5) :
    v = 0 ∨ v = Pi.single a 1 + Pi.single b 1 := by
  classical
  have hevenv : Even (sec4FOffCount a b v) := sec4FOffCount_even hab hv hvab
  have hnv0 : sec4FOffCount a b v = 0 := by
    rcases h1 with h1 | h1
    · have hoffu := sec4FOffCount_eq_zero_imp h1
      have hEq : sec4FOffCount a b (u + v) = sec4FOffCount a b v := by
        rw [sec4FOffCount_eq_filter, sec4FOffCount_eq_filter]
        congr 1
        apply Finset.filter_congr
        intro k hk
        simp only [sec4FOffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        constructor
        · intro h
          simpa only [Pi.add_apply, hoffu k hk.1 hk.2, zero_add] using h
        · intro h
          simpa only [Pi.add_apply, hoffu k hk.1 hk.2, zero_add] using h
      rcases h2 with h2 | h2
      · rw [hEq] at h2; exact h2
      · rw [hEq] at h2
        obtain ⟨m, hm⟩ := hevenv
        omega
    · have hoffu := sec4FOffCount_eq_five_imp hab h1
      have hcompl : sec4FOffCount a b (u + v) + sec4FOffCount a b v = 5 := by
        have hEq1 : sec4FOffCount a b (u + v)
            = ((sec4FOffSet a b).filter fun k => v k = 0).card := by
          rw [sec4FOffCount_eq_filter]
          congr 1
          apply Finset.filter_congr
          intro k hk
          simp only [sec4FOffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have huk : u k ≠ 0 := hoffu k hk.1 hk.2
          constructor
          · intro huv
            have hu1 : u k = 1 := sec4F_zmod2_eq_one_of_ne_zero huk
            by_contra hvk
            exact huv (by rw [Pi.add_apply, hu1, sec4F_zmod2_eq_one_of_ne_zero hvk]; decide)
          · intro hvk
            rw [Pi.add_apply, hvk, add_zero]
            exact huk
        have hEq2 : sec4FOffCount a b v
            = ((sec4FOffSet a b).filter fun k => ¬ (v k = 0)).card := by
          rw [sec4FOffCount_eq_filter]
        rw [hEq1, hEq2, Finset.card_filter_add_card_filter_not (p := fun k => v k = 0)]
        exact sec4FOffSet_card a b hab
      rcases h2 with h2 | h2
      · rw [h2] at hcompl
        obtain ⟨m, hm⟩ := hevenv
        omega
      · rw [h2] at hcompl
        omega
  have hv0 := sec4FOffCount_eq_zero_imp hnv0
  by_cases hc : v a = 0
  · left
    funext k
    by_cases hka : k = a
    · rw [hka, hc]; simp
    · by_cases hkb : k = b
      · rw [hkb, ← hvab, hc]; simp
      · exact hv0 k hka hkb
  · right
    funext k
    have hca : v a = 1 := sec4F_zmod2_eq_one_of_ne_zero hc
    by_cases hka : k = a
    · subst hka
      rw [hca, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
    · by_cases hkb : k = b
      · subst hkb
        rw [← hvab, hca, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same,
          zero_add]
      · rw [hv0 k hka hkb, Pi.add_apply, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb,
          add_zero]

end CFSG.OddStandard.SmallF3.Omega
