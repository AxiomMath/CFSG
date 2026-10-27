module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44AbsOrbit

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs

open Subgroup MulAction

variable {V : Type} [CommGroup V] {X M : Subgroup (MulAut V)} {t : V} {O : Fin 5 → Set V}

theorem mul_mem_orbit_of_two [Finite V] (hMX : M ≤ X) (hO : OrbitData M t O)
    {ν : MulAut V} (hνX : ν ∈ X) (hνt : ν t = t) (hν : (fun v => ν v) '' O 0 = O 1)
    (h1 : O 1 ⊆ orbit X t) (hrest : ∀ w ∈ orbit X t, w ≠ t → w ∈ O 0 ∨ w ∈ O 1) {a b : V}
    (ha : a ∈ orbit X t) (hb : b ∈ orbit X t) (hab : a ≠ b) : a * b ∈ orbit X t := by
  obtain ⟨g, hgX, rfl⟩ := mem_orbit_iff_exists.1 ha
  have hb' : g⁻¹ b ∈ orbit X t := apply_mem_orbit (X.inv_mem hgX) hb
  have hb't : g⁻¹ b ≠ t := by
    intro h
    apply hab
    have : b = g t := by rw [← h]; simp
    exact this.symm
  obtain ⟨x₀, hx₀⟩ := hO.isOrbit 0
  have hx₀O : x₀ ∈ O 0 := hx₀ ▸ mem_orbit_self x₀
  obtain ⟨y, hyX, hyt, hyx⟩ : ∃ y ∈ X, y t = t ∧ y x₀ = g⁻¹ b := by
    rcases hrest _ hb' hb't with h | h
    · rw [hx₀] at h
      obtain ⟨m, hmM, hm⟩ := mem_orbit_iff_exists.1 h
      exact ⟨m, hMX hmM, hO.fix m hmM, hm⟩
    · rw [← hν] at h
      obtain ⟨u, hu, hνu⟩ := h
      rw [hx₀] at hu
      obtain ⟨m, hmM, hm⟩ := mem_orbit_iff_exists.1 hu
      refine ⟨ν * m, X.mul_mem hνX (hMX hmM), ?_, ?_⟩
      · show ν (m t) = t
        rw [hO.fix m hmM, hνt]
      · show ν (m x₀) = _
        rw [hm]
        exact hνu
  have hprod : (g t) * b = (g * y) (t * x₀) := by
    have e1 : (g * y) t = g t := by
      show g (y t) = g t
      rw [hyt]
    have e2 : (g * y) x₀ = b := by
      show g (y x₀) = b
      rw [hyx]
      simp
    rw [map_mul, e1, e2]
  rw [hprod]
  refine apply_mem_orbit (X.mul_mem hgX hyX) ?_
  apply h1
  rw [hO.swap]
  exact ⟨x₀, hx₀O, rfl⟩

theorem not_card_45 [Finite V] (hV : Nat.card V = 2 ^ 11) (hsq : ∀ v : V, v ^ 2 = 1)
    (hMX : M ≤ X) (hO : OrbitData M t O)
    (hν : ∃ ν ∈ X, ν t = t ∧ (fun v => ν v) '' O 0 = O 1)
    (h1 : O 1 ⊆ orbit X t) (h2 : ¬ O 2 ⊆ orbit X t)
    (h3 : ¬ O 3 ⊆ orbit X t) (h4 : ¬ O 4 ⊆ orbit X t) (hcard : (orbit X t).ncard = 45) :
    False := by
  obtain ⟨ν, hνX, hνt, hν⟩ := hν
  have hΩ1 : (1 : V) ∉ orbit X t := one_notMem_orbit hO.ne_one
  have hrest : ∀ w ∈ orbit X t, w ≠ t → w ∈ O 0 ∨ w ∈ O 1 := by
    intro w hw hwt
    have hw1 : w ≠ 1 := fun h => hΩ1 (h ▸ hw)
    rcases hO.cover w hw1 with h | ⟨i, hi⟩
    · exact absurd h hwt
    · have hsub : O i ⊆ orbit X t := subset_of_mem (orbit_invariant hMX t) hO hi hw
      match i, hi, hsub with
      | 0, hi, _ => exact Or.inl hi
      | 1, hi, _ => exact Or.inr hi
      | 2, _, hsub => exact absurd hsub h2
      | 3, _, hsub => exact absurd hsub h3
      | 4, _, hsub => exact absurd hsub h4
  let H : Subgroup V :=
    { carrier := insert 1 (orbit X t)
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | ha
        · rw [one_mul]
          exact hb
        rcases hb with rfl | hb
        · rw [mul_one]
          exact Set.mem_insert_of_mem _ ha
        by_cases hab : a = b
        · subst hab
          left
          rw [← pow_two]
          exact hsq a
        · right
          exact mul_mem_orbit_of_two hMX hO hνX hνt hν h1 hrest ha hb hab
      one_mem' := Set.mem_insert _ _
      inv_mem' := by
        intro a ha
        have : a⁻¹ = a := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_two]
          exact hsq a
        rw [this]
        exact ha }
  have hH : Nat.card H = 46 := by
    have : Nat.card H = (H : Set V).ncard := Nat.card_coe_set_eq (H : Set V)
    rw [this]
    show (insert 1 (orbit X t)).ncard = 46
    rw [Set.ncard_insert_of_notMem hΩ1 (Set.toFinite _), hcard]
  have := Subgroup.card_subgroup_dvd_card H
  rw [hH, hV] at this
  exact absurd this (by decide)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs
