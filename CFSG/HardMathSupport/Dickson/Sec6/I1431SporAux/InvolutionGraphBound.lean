module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

section Graph

variable {G : Type*} [Group G]

theorem dihedral_center {u u' : G} (hu : u * u = 1) (hu' : u' * u' = 1) {n : ℕ}
    (hn : orderOf (u * u') = n) (hn2 : 2 ∣ n) (hn4 : 4 ≤ n) :
    ((u * u') ^ (n / 2)) * ((u * u') ^ (n / 2)) = 1 ∧ (u * u') ^ (n / 2) ≠ 1 ∧
      ((u * u') ^ (n / 2)) * u = u * ((u * u') ^ (n / 2)) ∧
      ((u * u') ^ (n / 2)) * u' = u' * ((u * u') ^ (n / 2)) ∧ (u * u') ^ (n / 2) ≠ u ∧
      (u * u') ^ (n / 2) ≠ u' ∧ u' ≠ u * (u * u') ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn2
  have hm : 2 ≤ m := by omega
  set g := u * u' with hg
  have hgn : g ^ (2 * m) = 1 := by rw [← hn]; exact pow_orderOf_eq_one g
  have hhalf : 2 * m / 2 = m := by omega
  rw [hhalf]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hu'i : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'
  have hginv : g⁻¹ = u' * u := by rw [hg, mul_inv_rev, hui, hu'i]
  have hugu : u * g * u⁻¹ = g⁻¹ := by
    rw [hui, hginv, hg]
    calc u * (u * u') * u = (u * u) * u' * u := by group
      _ = u' * u := by rw [hu, one_mul]
  have hu'gu' : u' * g * u'⁻¹ = g⁻¹ := by
    rw [hu'i, hginv, hg]
    calc u' * (u * u') * u' = u' * u * (u' * u') := by group
      _ = u' * u := by rw [hu', mul_one]
  have hγ2 : g ^ m * g ^ m = 1 := by rw [← pow_add, ← two_mul]; exact hgn
  have hγinv : (g ^ m)⁻¹ = g ^ m := inv_eq_of_mul_eq_one_right hγ2
  have hγne : g ^ m ≠ 1 := by
    intro h
    have : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [hn] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hcu : g ^ m * u = u * g ^ m := by
    have h1 : u * g ^ m * u⁻¹ = (g⁻¹) ^ m := by rw [← conj_pow, hugu]
    rw [inv_pow, hγinv] at h1
    calc g ^ m * u = (u * g ^ m * u⁻¹) * u := by rw [h1]
      _ = u * g ^ m := by group
  have hcu' : g ^ m * u' = u' * g ^ m := by
    have h1 : u' * g ^ m * u'⁻¹ = (g⁻¹) ^ m := by rw [← conj_pow, hu'gu']
    rw [inv_pow, hγinv] at h1
    calc g ^ m * u' = (u' * g ^ m * u'⁻¹) * u' := by rw [h1]
      _ = u' * g ^ m := by group
  have hgcomm : Commute (g ^ m) g := (Commute.refl g).pow_left m
  refine ⟨hγ2, hγne, hcu, hcu', ?_, ?_, ?_⟩
  · intro h
    have h1 : u * g = g * u := by
      have := hgcomm.eq
      rw [h] at this
      exact this
    have h2 : g⁻¹ = g := by
      calc g⁻¹ = u * g * u⁻¹ := hugu.symm
        _ = g * u * u⁻¹ := by rw [h1]
        _ = g := by group
    have h3 : g * g = 1 := by
      calc g * g = g⁻¹ * g := by rw [h2]
        _ = 1 := inv_mul_cancel g
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rw [hn] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · intro h
    have h1 : u' * g = g * u' := by
      have := hgcomm.eq
      rw [h] at this
      exact this
    have h2 : g⁻¹ = g := by
      calc g⁻¹ = u' * g * u'⁻¹ := hu'gu'.symm
        _ = g * u' * u'⁻¹ := by rw [h1]
        _ = g := by group
    have h3 : g * g = 1 := by
      calc g * g = g⁻¹ * g := by rw [h2]
        _ = 1 := inv_mul_cancel g
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rw [hn] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · intro h
    have hcomm : u' * u = u * u' := by
      rw [h]
      calc u * g ^ m * u = u * (g ^ m * u) := mul_assoc _ _ _
        _ = u * (u * g ^ m) := by rw [hcu]
    have h3 : g * g = 1 := by
      calc g * g = u * u' * (u * u') := by rw [hg]
        _ = u * (u' * u) * u' := by group
        _ = u * (u * u') * u' := by rw [hcomm]
        _ = (u * u) * (u' * u') := by group
        _ = 1 := by rw [hu, hu', one_mul]
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rw [hn] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

variable [Finite G]

theorem ncard_involutions_le {x : G} {d e : ℕ}
    (hord : ∀ u u' : G, u * u = 1 → u ≠ 1 → u * x = x * u → u' * u' = 1 → u' ≠ 1 →
      u' * x = x * u' → (orderOf (u * u') = 1 ∨ orderOf (u * u') = 2 ∨ orderOf (u * u') = 3 ∨
        orderOf (u * u') = 4 ∨ orderOf (u * u') = 6))
    (hN : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u →
      {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ u' ≠ u ∧ u' * u = u * u'}.ncard ≤ d)
    (h3 : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u →
      {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ orderOf (u * u') = 3}.ncard ≤ e) :
    {u : G | u * u = 1 ∧ u ≠ 1 ∧ u * x = x * u}.ncard ≤ 1 + d + e + d * (d - 2) := by
  classical
  set X : Set G := {u : G | u * u = 1 ∧ u ≠ 1 ∧ u * x = x * u} with hX
  let N : G → Set G := fun u =>
    {u' : G | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ u' ≠ u ∧ u' * u = u * u'}
  by_cases hne : X.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp
  obtain ⟨u₀, hu₀⟩ := hne
  obtain ⟨hu₀2, hu₀1, hu₀x⟩ := hu₀
  let O3 : Set G := {u' | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧ orderOf (u₀ * u') = 3}
  let O46 : Set G := {u' | u' * u' = 1 ∧ u' ≠ 1 ∧ u' * x = x * u' ∧
    (orderOf (u₀ * u') = 4 ∨ orderOf (u₀ * u') = 6)}
  have hcover : X ⊆ {u₀} ∪ N u₀ ∪ O3 ∪ O46 := by
    intro u' hu'
    obtain ⟨hu'2, hu'1, hu'x⟩ := hu'
    rcases hord u₀ u' hu₀2 hu₀1 hu₀x hu'2 hu'1 hu'x with h | h | h | h | h
    · left; left; left
      have h1 : u₀ * u' = 1 := orderOf_eq_one_iff.1 h
      have : u' = u₀⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_eq_of_mul_eq_one_right hu₀2]
      rfl
    · left; left; right
      have hq : (u₀ * u') * (u₀ * u') = 1 := by
        rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [h])
      refine ⟨hu'2, hu'1, hu'x, ?_, ?_⟩
      · intro heq
        rw [heq, hu₀2] at h
        simp at h
      · have : u₀ * u' = u' * u₀ := by
          have hu₀i : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀2
          have hu'i : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'2
          have h1 : u₀ * u' = (u₀ * u')⁻¹ := eq_inv_of_mul_eq_one_left hq
          rw [h1, mul_inv_rev, hu₀i, hu'i]
        exact this.symm
    · left; right; exact ⟨hu'2, hu'1, hu'x, h⟩
    · right; exact ⟨hu'2, hu'1, hu'x, Or.inl h⟩
    · right; exact ⟨hu'2, hu'1, hu'x, Or.inr h⟩
  have h46 : O46 ⊆ ⋃ γ ∈ (Set.toFinite (N u₀)).toFinset, (N γ \ {u₀, u₀ * γ}) := by
    intro u' hu'
    obtain ⟨hu'2, hu'1, hu'x, hn⟩ := hu'
    have hn2 : 2 ∣ orderOf (u₀ * u') := by rcases hn with h | h <;> rw [h] <;> norm_num
    have hn4 : 4 ≤ orderOf (u₀ * u') := by rcases hn with h | h <;> rw [h] <;> norm_num
    obtain ⟨hγ2, hγ1, hγu, hγu', hγu0, hγu'ne, hu'ne⟩ :=
      dihedral_center hu₀2 hu'2 rfl hn2 hn4
    set γ := (u₀ * u') ^ (orderOf (u₀ * u') / 2) with hγdef
    have hγx : γ * x = x * γ := by
      have hc : Commute (u₀ * u') x := (show Commute u₀ x from hu₀x).mul_left
        (show Commute u' x from hu'x)
      exact (hc.pow_left _).eq
    have hγN : γ ∈ N u₀ := ⟨hγ2, hγ1, hγx, hγu0, hγu⟩
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    refine ⟨γ, hγN, ⟨hu'2, hu'1, hu'x, hγu'ne.symm, hγu'.symm⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, hu'ne⟩
    intro heq
    rw [heq, hu₀2] at hn
    simp at hn
  have hN46 : ∀ γ ∈ (Set.toFinite (N u₀)).toFinset, (N γ \ {u₀, u₀ * γ}).ncard ≤ d - 2 := by
    intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    obtain ⟨hγ2, hγ1, hγx, hγu0, hγu⟩ := hγ
    have hγi : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
    have hu₀N : u₀ ∈ N γ := ⟨hu₀2, hu₀1, hu₀x, fun h => hγu0 h.symm, hγu.symm⟩
    have hu₀γne : u₀ * γ ≠ u₀ := by
      intro h
      apply hγ1
      have := congrArg (u₀⁻¹ * ·) h
      simpa using this
    have hu₀γN : u₀ * γ ∈ N γ := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · calc u₀ * γ * (u₀ * γ) = u₀ * (γ * u₀) * γ := by group
          _ = u₀ * (u₀ * γ) * γ := by rw [hγu]
          _ = (u₀ * u₀) * (γ * γ) := by group
          _ = 1 := by rw [hu₀2, hγ2, one_mul]
      · intro h
        have h1 : u₀ = γ⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [hγi] at h1
        exact hγu0 h1.symm
      · have hc : Commute (u₀ * γ) x := (show Commute u₀ x from hu₀x).mul_left
          (show Commute γ x from hγx)
        exact hc.eq
      · intro h
        apply hu₀1
        have := congrArg (γ⁻¹ * ·) h
        simpa [hγi] using this
      · calc u₀ * γ * γ = u₀ * (γ * γ) := mul_assoc _ _ _
          _ = u₀ := by rw [hγ2, mul_one]
          _ = γ * (γ * u₀) := by rw [← mul_assoc, hγ2, one_mul]
          _ = γ * (u₀ * γ) := by rw [hγu]
    have hsub : ({u₀, u₀ * γ} : Set G) ⊆ N γ := by
      intro y hy
      rcases hy with rfl | rfl
      · exact hu₀N
      · exact hu₀γN
    have hcard : ({u₀, u₀ * γ} : Set G).ncard = 2 :=
      Set.ncard_pair (fun h => hu₀γne h.symm)
    have hd : (N γ).ncard ≤ d := hN γ hγ2 hγ1 hγx
    rw [Set.ncard_diff hsub (Set.toFinite _), hcard]
    omega
  have hO46 : O46.ncard ≤ d * (d - 2) := by
    calc O46.ncard ≤ (⋃ γ ∈ (Set.toFinite (N u₀)).toFinset, (N γ \ {u₀, u₀ * γ})).ncard :=
          Set.ncard_le_ncard h46 (Set.toFinite _)
      _ ≤ ∑ γ ∈ (Set.toFinite (N u₀)).toFinset, (N γ \ {u₀, u₀ * γ}).ncard :=
          Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ γ ∈ (Set.toFinite (N u₀)).toFinset, (d - 2) := Finset.sum_le_sum hN46
      _ = (N u₀).ncard * (d - 2) := by
          rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      _ ≤ d * (d - 2) := Nat.mul_le_mul_right _ (hN u₀ hu₀2 hu₀1 hu₀x)
  have hO3 : O3.ncard ≤ e := h3 u₀ hu₀2 hu₀1 hu₀x
  have hNu : (N u₀).ncard ≤ d := hN u₀ hu₀2 hu₀1 hu₀x
  calc X.ncard ≤ ({u₀} ∪ N u₀ ∪ O3 ∪ O46).ncard := Set.ncard_le_ncard hcover (Set.toFinite _)
    _ ≤ ({u₀} ∪ N u₀ ∪ O3).ncard + O46.ncard := Set.ncard_union_le _ _
    _ ≤ (({u₀} ∪ N u₀).ncard + O3.ncard) + O46.ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ (({u₀} : Set G).ncard + (N u₀).ncard + O3.ncard) + O46.ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ 1 + d + e + d * (d - 2) := by
        rw [Set.ncard_singleton]; omega

end Graph

end CFSG.HardMathSupport.Dickson.Sec6.I1431
