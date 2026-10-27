module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt_numeric_cases {n r : ℕ} (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    (h : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 360 ∨
      2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 1440) : False := by
  generalize hm : n - 2 * r = m at h
  have hP : 0 < 2 ^ (r - 1) * r.factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos r)
  have hr5 : r ≤ 5 := by
    by_contra hh
    have h1 : 720 ≤ r.factorial := by
      have := Nat.factorial_le (show 6 ≤ r by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h2 : 32 ≤ 2 ^ (r - 1) := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 32 * 720 ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 32 * 720 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h3.trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos m))
    omega
  have hm7 : m ≤ 7 := by
    by_contra hh
    have h1 : 40320 ≤ m.factorial := by
      have := Nat.factorial_le (show 8 ≤ m by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h4 : 40320 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h1.trans (Nat.le_mul_of_pos_left _ hP)
    omega
  interval_cases r <;> interval_cases m <;> norm_num [Nat.factorial] at h

theorem alt_numeric_720 {n r : ℕ} (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    (h : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 720) : r = 1 ∧ n = 8 := by
  generalize hm : n - 2 * r = m at h
  have hP : 0 < 2 ^ (r - 1) * r.factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos r)
  have hr4 : r ≤ 4 := by
    by_contra hh
    have h1 : 120 ≤ r.factorial := by
      have := Nat.factorial_le (show 5 ≤ r by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h2 : 8 ≤ 2 ^ (r - 1) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 8 * 120 ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 8 * 120 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h3.trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos m))
    omega
  have hm6 : m ≤ 6 := by
    by_contra hh
    have h1 : 5040 ≤ m.factorial := by
      have := Nat.factorial_le (show 7 ≤ m by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h4 : 5040 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h1.trans (Nat.le_mul_of_pos_left _ hP)
    omega
  interval_cases r <;> interval_cases m <;> norm_num [Nat.factorial] at h <;> omega

private theorem alt8_orderOf_eq_six {G : Type*} [Group G] {g : G} (h6 : g ^ 6 = 1)
    (h2 : g ^ 2 ≠ 1) (h3 : g ^ 3 ≠ 1) : orderOf g = 6 := by
  have hd : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hk : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hle : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  generalize orderOf g = k at hd hk hle ⊢
  interval_cases k
  · norm_num at hd
  · rw [pow_one] at hk
    subst hk
    exact absurd (one_pow 2) h2
  · exact absurd hk h2
  · exact absurd hk h3
  · norm_num at hd
  · norm_num at hd
  · rfl

private theorem alt8_transport {π π₀ g₀ : Equiv.Perm (Fin 8)} (hconj : IsConj π π₀)
    (hsign : Equiv.Perm.sign g₀ = 1) (hcomm : g₀ * π₀ = π₀ * g₀) (hord : orderOf g₀ = 6) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ g * π = π * g ∧ orderOf g = 6 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hπ : π = c⁻¹ * π₀ * c := by rw [← hc]; group
  have hS : SemiconjBy c⁻¹ g₀ (c⁻¹ * g₀ * c) := by
    unfold SemiconjBy
    group
  refine ⟨c⁻¹ * g₀ * c, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hsign, mul_one, inv_mul_cancel]
  · rw [hπ]
    calc c⁻¹ * g₀ * c * (c⁻¹ * π₀ * c) = c⁻¹ * (g₀ * π₀) * c := by group
      _ = c⁻¹ * (π₀ * g₀) * c := by rw [hcomm]
      _ = c⁻¹ * π₀ * c * (c⁻¹ * g₀ * c) := by group
  · rw [← SemiconjBy.orderOf_eq c⁻¹ hS, hord]

private theorem alt8_ct_swap {x y : Fin 8} (h : x ≠ y) :
    (Equiv.swap x y).cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.1 (Equiv.Perm.swap_isSwap_iff.2 h)

private theorem alt8_ct_two :
    (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3).cycleType = Multiset.replicate 2 2 :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem alt8_ct_three :
    (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5).cycleType =
      Multiset.replicate 3 2 := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) (Equiv.swap 4 5) :=
    Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  rw [hd.cycleType_mul, alt8_ct_two, alt8_ct_swap (by decide : (4 : Fin 8) ≠ 5)]
  all_goals rfl

private theorem alt8_ct_four :
    (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7).cycleType =
      Multiset.replicate 4 2 := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5)
      (Equiv.swap 6 7) :=
    Equiv.Perm.Disjoint.mul_left
      (Equiv.Perm.Disjoint.mul_left (Equiv.Perm.disjoint_swap_swap (by decide))
        (Equiv.Perm.disjoint_swap_swap (by decide)))
      (Equiv.Perm.disjoint_swap_swap (by decide))
  rw [hd.cycleType_mul, alt8_ct_three, alt8_ct_swap (by decide : (6 : Fin 8) ≠ 7)]
  all_goals rfl

private theorem alt8_std_one : ∃ π₀ g₀ : Equiv.Perm (Fin 8),
    π₀.cycleType = Multiset.replicate 1 2 ∧ Equiv.Perm.sign g₀ = 1 ∧ g₀ * π₀ = π₀ * g₀ ∧
      orderOf g₀ = 6 :=
  ⟨Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 5 6 * (Equiv.swap 2 3 * Equiv.swap 3 4),
    alt8_ct_swap (by decide), by decide, by decide,
    alt8_orderOf_eq_six (by decide) (by decide) (by decide)⟩

private theorem alt8_std_two : ∃ π₀ g₀ : Equiv.Perm (Fin 8),
    π₀.cycleType = Multiset.replicate 2 2 ∧ Equiv.Perm.sign g₀ = 1 ∧ g₀ * π₀ = π₀ * g₀ ∧
      orderOf g₀ = 6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3 * (Equiv.swap 4 5 * Equiv.swap 5 6),
    alt8_ct_two, by decide, by decide, alt8_orderOf_eq_six (by decide) (by decide) (by decide)⟩

private theorem alt8_std_three : ∃ π₀ g₀ : Equiv.Perm (Fin 8),
    π₀.cycleType = Multiset.replicate 3 2 ∧ Equiv.Perm.sign g₀ = 1 ∧ g₀ * π₀ = π₀ * g₀ ∧
      orderOf g₀ = 6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5,
    Equiv.swap 0 2 * Equiv.swap 2 4 * (Equiv.swap 1 3 * Equiv.swap 3 5) * Equiv.swap 6 7 *
      (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5),
    alt8_ct_three, by decide, by decide,
    alt8_orderOf_eq_six (by decide +kernel) (by decide) (by decide)⟩

private theorem alt8_std_four : ∃ π₀ g₀ : Equiv.Perm (Fin 8),
    π₀.cycleType = Multiset.replicate 4 2 ∧ Equiv.Perm.sign g₀ = 1 ∧ g₀ * π₀ = π₀ * g₀ ∧
      orderOf g₀ = 6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7,
    Equiv.swap 0 2 * Equiv.swap 2 4 * (Equiv.swap 1 3 * Equiv.swap 3 5) *
      (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7),
    alt8_ct_four, by decide, by decide,
    alt8_orderOf_eq_six (by decide +kernel) (by decide) (by decide)⟩

private theorem alt8_centralizer_six (π : Equiv.Perm (Fin 8)) (h : π * π = 1) (h1 : π ≠ 1) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ g * π = π * g ∧ orderOf g = 6 := by
  obtain ⟨a, ha1, ha2, hc⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.cycleType_eq_replicate_two π h h1
  have ha4 : a ≤ 4 := by omega
  interval_cases a
  · obtain ⟨π₀, g₀, h₀, hs, hcm, ho⟩ := alt8_std_one
    exact alt8_transport (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans h₀.symm)) hs hcm ho
  · obtain ⟨π₀, g₀, h₀, hs, hcm, ho⟩ := alt8_std_two
    exact alt8_transport (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans h₀.symm)) hs hcm ho
  · obtain ⟨π₀, g₀, h₀, hs, hcm, ho⟩ := alt8_std_three
    exact alt8_transport (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans h₀.symm)) hs hcm ho
  · obtain ⟨π₀, g₀, h₀, hs, hcm, ho⟩ := alt8_std_four
    exact alt8_transport (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans h₀.symm)) hs hcm ho

theorem alt_eight_order_six {S : Type} [Group S] [Finite S] (θ : S ≃* alternatingGroup (Fin 8))
    {σ : MulAut S} (hσ : orderOf σ = 2) : ∃ x : ↥(fixedSubgroup σ), orderOf x = 6 := by
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by decide)
  have hτsq : ∀ x : S, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut S => f x) hσ2
    simpa using this
  let τ' : MulAut (alternatingGroup (Fin 8)) := θ.symm.trans ((σ : S ≃* S).trans θ)
  have hτ' : ∀ a, τ' a = θ (σ (θ.symm a)) := fun _ => rfl
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 τ'
  have hsq : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one]
    ext a
    simp [hτ', hτsq]
  have hne : π ≠ 1 := by
    rintro rfl
    apply hσ1
    ext x
    have h3 : τ' (θ x) = θ x := by rw [← hπ]; simp
    rw [hτ'] at h3
    simpa using h3
  have key : ∀ x : S, σ x = x ↔
      π * ((θ x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        ((θ x : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) * π := by
    intro x
    have h1' : τ' (θ x) = θ (σ x) := by simp [hτ']
    constructor
    · intro hx
      have h3 : MulAut.conjNormal π (θ x) = θ x := by rw [hπ, h1', hx]
      have h4 := congrArg Subtype.val h3
      rw [MulAut.conjNormal_apply] at h4
      exact mul_inv_eq_iff_eq_mul.1 h4
    · intro h
      apply θ.injective
      rw [← h1', ← hπ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, h, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨g, hsg, hcomm, hord⟩ := alt8_centralizer_six π hsq hne
  have hg : g ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 hsg
  refine ⟨⟨θ.symm ⟨g, hg⟩, ?_⟩, ?_⟩
  · show σ (θ.symm ⟨g, hg⟩) = θ.symm ⟨g, hg⟩
    rw [key, MulEquiv.apply_symm_apply]
    exact hcomm.symm
  · rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq θ.symm, Subgroup.orderOf_mk, hord]

theorem alt_fixed_false {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 7 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hc : Nat.card ↥(fixedSubgroup σ) = 360 ∨ Nat.card ↥(fixedSubgroup σ) = 1440 ∨
      (Nat.card ↥(fixedSubgroup σ) = 720 ∧ ∀ x : ↥(fixedSubgroup σ), orderOf x ≠ 6)) : False := by
  obtain ⟨r, hr1, hrn, hcard⟩ := card_fixedSubgroup_alt hn θ hσ
  rcases hc with h360 | h1440 | ⟨h720, hno6⟩
  · exact alt_numeric_cases hr1 hrn (Or.inl (hcard.symm.trans h360))
  · exact alt_numeric_cases hr1 hrn (Or.inr (hcard.symm.trans h1440))
  · obtain ⟨-, hn8⟩ := alt_numeric_720 hr1 hrn (hcard.symm.trans h720)
    subst hn8
    obtain ⟨x, hx⟩ := alt_eight_order_six θ hσ
    exact hno6 x hx

end CFSG.ComponentClassification.CatFC
