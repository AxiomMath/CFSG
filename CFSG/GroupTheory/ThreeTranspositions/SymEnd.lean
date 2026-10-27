module

public import CFSG.GroupTheory.ThreeTranspositions.Basic

public section

namespace CFSG.GroupTheory.ThreeTranspositions

theorem hasE9_perm_fin_of_six_le {m : ℕ} (hm : 6 ≤ m) : HasE9 (Equiv.Perm (Fin m)) := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  let i3 : Fin m := ⟨3, by omega⟩
  let i4 : Fin m := ⟨4, by omega⟩
  let i5 : Fin m := ⟨5, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have h34 : i3 ≠ i4 := by simp [i3, i4]
  have h35 : i3 ≠ i5 := by simp [i3, i5]
  have h45 : i4 ≠ i5 := by simp [i4, i5]
  have h30 : i3 ≠ i0 := by simp [i3, i0]
  have h31 : i3 ≠ i1 := by simp [i3, i1]
  have h32 : i3 ≠ i2 := by simp [i3, i2]
  have h40 : i4 ≠ i0 := by simp [i4, i0]
  have h41 : i4 ≠ i1 := by simp [i4, i1]
  have h42 : i4 ≠ i2 := by simp [i4, i2]
  have h50 : i5 ≠ i0 := by simp [i5, i0]
  have h51 : i5 ≠ i1 := by simp [i5, i1]
  have h52 : i5 ≠ i2 := by simp [i5, i2]
  let x : Equiv.Perm (Fin m) := Equiv.swap i0 i1 * Equiv.swap i0 i2
  let y : Equiv.Perm (Fin m) := Equiv.swap i3 i4 * Equiv.swap i3 i5
  have hx3 : Equiv.Perm.IsThreeCycle x :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := i0) (b := i1) (c := i2) h01 h02 h12
  have hy3 : Equiv.Perm.IsThreeCycle y :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := i3) (b := i4) (c := i5) h34 h35 h45
  have hxfix : ∀ z : Fin m, z ≠ i0 → z ≠ i1 → z ≠ i2 → x z = z := by
    intro z h0 h1 h2
    show (Equiv.swap i0 i1 * Equiv.swap i0 i2) z = z
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h0 h2,
      Equiv.swap_apply_of_ne_of_ne h0 h1]
  have hyfix : ∀ z : Fin m, z ≠ i3 → z ≠ i4 → z ≠ i5 → y z = z := by
    intro z h3 h4 h5
    show (Equiv.swap i3 i4 * Equiv.swap i3 i5) z = z
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h5,
      Equiv.swap_apply_of_ne_of_ne h3 h4]
  have hdisj : Equiv.Perm.Disjoint x y := by
    intro z
    by_cases hz : z = i3 ∨ z = i4 ∨ z = i5
    · left
      rcases hz with h3 | h4 | h5
      · rw [h3]; exact hxfix i3 h30 h31 h32
      · rw [h4]; exact hxfix i4 h40 h41 h42
      · rw [h5]; exact hxfix i5 h50 h51 h52
    · right
      simp only [not_or] at hz
      exact hyfix z hz.1 hz.2.1 hz.2.2
  have hfix3 : x i3 = i3 := hxfix i3 h30 h31 h32
  have hyne3 : y i3 ≠ i3 := by
    show (Equiv.swap i3 i4 * Equiv.swap i3 i5) i3 ≠ i3
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne h35.symm h45.symm]
    exact h35.symm
  refine ⟨x, y, hx3.orderOf, hy3.orderOf, hdisj.commute, ?_⟩
  intro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hyne3 (by rw [← hn, Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix3 n])

theorem card_eq_six_or_one_twenty_of_mulEquiv_perm {X : Type*} [Group X] {m : ℕ}
    (hm : m = 3 ∨ 5 ≤ m) (φ : X ≃* Equiv.Perm (Fin m)) (hX : ¬ HasE9 X) :
    Nat.card X = 6 ∨ Nat.card X = 120 := by
  have hcard : Nat.card X = Nat.card (Equiv.Perm (Fin m)) := Nat.card_congr φ.toEquiv
  rcases hm with rfl | h
  · left
    rw [hcard, Nat.card_perm, Nat.card_fin]
    decide
  rcases eq_or_lt_of_le h with rfl | h6
  · right
    rw [hcard, Nat.card_perm, Nat.card_fin]
    decide
  · exfalso
    have h6' : 6 ≤ m := by omega
    exact hX (HasE9.map_injective φ.symm.toMonoidHom φ.symm.injective
      (hasE9_perm_fin_of_six_le h6'))

end CFSG.GroupTheory.ThreeTranspositions
