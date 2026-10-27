module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesSym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal

variable {m : ℕ}

theorem i28_14_sym_coord (σ : Equiv.Perm (Fin m)) (i x z : Fin m) :
    (permCoord σ (pairVec i x : Fin m → ZMod 2) + (pairVec i x : Fin m → ZMod 2)) z =
      (if σ⁻¹ z = i then 1 else 0) + (if σ⁻¹ z = x then 1 else 0) +
        ((if z = i then 1 else 0) + (if z = x then 1 else 0)) := by
  simp [permCoord_apply, coe_pairVec, Pi.single_apply]

theorem i28_14_sym_not_const (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)} {i x : Fin m}
    (hi : σ i ≠ i) (hxi : x ≠ i) (hxj : x ≠ σ i) :
    ¬ ∃ c : ZMod 2, permCoord σ (pairVec i x : Fin m → ZMod 2) + (pairVec i x : Fin m → ZMod 2) =
      fun _ => c := by
  rintro ⟨c, hc⟩
  obtain ⟨z, hz⟩ := mclt_exists_notMem {σ i, σ x, i, x}
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have h1 := congrFun hc (σ i)
  have h2 := congrFun hc z
  rw [i28_14_sym_coord] at h1 h2
  have e1 : σ.symm z ≠ i := fun h => hz1 (by rw [← h]; simp)
  have e2 : σ.symm z ≠ x := fun h => hz2 (by rw [← h]; simp)
  simp [e1, e2, hz3, hz4, hxi.symm, hi, Ne.symm hxj] at h1 h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

theorem i28_14_sym_coord_add (σ : Equiv.Perm (Fin m)) (i x y z : Fin m) :
    (permCoord σ (pairVec i x : Fin m → ZMod 2) + (pairVec i x : Fin m → ZMod 2) +
      (permCoord σ (pairVec i y : Fin m → ZMod 2) + (pairVec i y : Fin m → ZMod 2))) z =
      ((if σ⁻¹ z = x then 1 else 0) + (if σ⁻¹ z = y then 1 else 0)) +
        ((if z = x then 1 else 0) + (if z = y then 1 else 0)) := by
  rw [Pi.add_apply, i28_14_sym_coord, i28_14_sym_coord]
  have key : ∀ A B C D E F : ZMod 2, A + B + (C + D) + (A + E + (C + F)) = B + E + (D + F) := by
    decide
  exact key _ _ _ _ _ _

theorem i28_14_sym_eq_of_const_sum (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)} {i l a : Fin m}
    (hl : σ l ≠ l) (hla : l ≠ a)
    (h : ∃ c : ZMod 2, permCoord σ (pairVec i l : Fin m → ZMod 2) + (pairVec i l : Fin m → ZMod 2) +
      (permCoord σ (pairVec i a : Fin m → ZMod 2) + (pairVec i a : Fin m → ZMod 2)) =
        fun _ => c) : σ l = a := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨z, hz⟩ := mclt_exists_notMem {σ l, σ a, l, a}
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have h1 := congrFun hc (σ l)
  have h2 := congrFun hc z
  rw [i28_14_sym_coord_add] at h1 h2
  have e1 : σ.symm z ≠ l := fun h => hz1 (by rw [← h]; simp)
  have e2 : σ.symm z ≠ a := fun h => hz2 (by rw [← h]; simp)
  by_contra hne
  simp [e1, e2, hz3, hz4] at h2
  simp [hl, hla, hne] at h1
  rw [← h2] at h1
  exact absurd h1 (by decide)

theorem i28_14_sym_swap_of_Q (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)} (hσ : σ ≠ 1)
    (Q : ∀ y₁ y₂ : sumZero m,
      (∃ c : ZMod 2, permCoord σ (y₁ : Fin m → ZMod 2) + (y₁ : Fin m → ZMod 2) = fun _ => c) ∨
      (∃ c : ZMod 2, permCoord σ (y₂ : Fin m → ZMod 2) + (y₂ : Fin m → ZMod 2) = fun _ => c) ∨
      (∃ c : ZMod 2, permCoord σ (y₁ : Fin m → ZMod 2) + (y₁ : Fin m → ZMod 2) +
        (permCoord σ (y₂ : Fin m → ZMod 2) + (y₂ : Fin m → ZMod 2)) = fun _ => c)) :
    ∃ i j : Fin m, i ≠ j ∧ σ = Equiv.swap i j := by
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra! h
    exact hσ (Equiv.ext h)
  have hfix : ∀ l, l ≠ i → l ≠ σ i → σ l = l := by
    intro l hli hlj
    by_contra hl
    obtain ⟨a, ha⟩ := mclt_exists_notMem {i, σ i, l}
      (lt_of_le_of_lt Finset.card_le_three (by omega))
    obtain ⟨b, hb⟩ := mclt_exists_notMem {i, σ i, l, a}
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
    obtain ⟨hai, haj, hal⟩ := ha
    obtain ⟨hbi, hbj, hbl, hba⟩ := hb
    have key : ∀ x, x ≠ i → x ≠ σ i → ∀ y, y ≠ i → y ≠ σ i → x ≠ y → σ x ≠ x →
        (∃ c : ZMod 2, permCoord σ (pairVec i x : Fin m → ZMod 2) +
          (pairVec i x : Fin m → ZMod 2) + (permCoord σ (pairVec i y : Fin m → ZMod 2) +
            (pairVec i y : Fin m → ZMod 2)) = fun _ => c) → σ x = y := by
      intro x hx1 hx2 y hy1 hy2 hxy hsx hc
      exact i28_14_sym_eq_of_const_sum hm hsx hxy hc
    have getc : ∀ y, y ≠ i → y ≠ σ i → ∀ x, x ≠ i → x ≠ σ i → x ≠ y → σ x ≠ x → σ x = y := by
      intro y hy1 hy2 x hx1 hx2 hxy hsx
      rcases Q (pairVec i x) (pairVec i y) with h | h | h
      · exact absurd h (i28_14_sym_not_const hm hi hx1 hx2)
      · exact absurd h (i28_14_sym_not_const hm hi hy1 hy2)
      · exact key x hx1 hx2 y hy1 hy2 hxy hsx h
    have e1 := getc a hai haj l hli hlj (Ne.symm hal) hl
    have e2 := getc b hbi hbj l hli hlj (Ne.symm hbl) hl
    exact hba (e2.symm.trans e1)
  have hij : i ≠ σ i := hi.symm
  have hj : σ (σ i) = i := by
    by_contra h
    have hj1 : σ (σ i) ≠ σ i := fun h' => hij (σ.injective h').symm
    have := hfix (σ (σ i)) h hj1
    exact hj1 (σ.injective this)
  refine ⟨i, σ i, hij, Equiv.ext fun z => ?_⟩
  by_cases hz1 : z = i
  · subst hz1
    rw [Equiv.swap_apply_left]
  by_cases hz2 : z = σ i
  · subst hz2
    rw [Equiv.swap_apply_right, hj]
  rw [Equiv.swap_apply_of_ne_of_ne hz1 hz2, hfix z hz1 hz2]

end CFSG.HardMathSupport.Solomon.Coordinator
