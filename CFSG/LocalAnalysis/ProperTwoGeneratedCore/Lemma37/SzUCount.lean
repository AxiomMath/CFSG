module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {X : Type*} [Group X]

section Product

variable {P R T : Subgroup X}

theorem eq_and_eq_of_mul_eq_mul_of_disjoint (hdisj : ∀ g ∈ R, g ∈ T → g = 1) {x x' k k' : X}
    (hx : x ∈ R) (hx' : x' ∈ R) (hk : k ∈ T) (hk' : k' ∈ T) (h : x * k = x' * k') :
    x = x' ∧ k = k' := by
  have h1 : x'⁻¹ * x = k' * k⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * k) * k⁻¹ := by group
      _ = x'⁻¹ * (x' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have h2 := hdisj _ (R.mul_mem (R.inv_mem hx') hx) (h1 ▸ T.mul_mem hk' (T.inv_mem hk))
  rw [inv_mul_eq_one] at h2
  subst h2
  exact ⟨rfl, mul_left_cancel h⟩

theorem card_sq_mul_eq_of_internal_prod (hRP : R ≤ P) (hTP : T ≤ P)
    (hcomm : ∀ x ∈ R, ∀ k ∈ T, x * k = k * x) (hdisj : ∀ g ∈ R, g ∈ T → g = 1)
    (hgen : ∀ w ∈ P, ∃ x ∈ R, ∃ k ∈ T, x * k = w) {x₀ k₀ : X} (hx₀ : x₀ ∈ R) (hk₀ : k₀ ∈ T) :
    Nat.card {w : X // w ∈ P ∧ w ^ 2 = x₀ * k₀} =
      Nat.card {x : X // x ∈ R ∧ x ^ 2 = x₀} * Nat.card {k : X // k ∈ T ∧ k ^ 2 = k₀} := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective (fun p => ⟨p.1.1 * p.2.1,
    P.mul_mem (hRP p.1.2.1) (hTP p.2.2.1), ?_⟩) ⟨?_, ?_⟩
  · rw [Commute.mul_pow (hcomm _ p.1.2.1 _ p.2.2.1) 2, p.1.2.2, p.2.2.2]
  · intro p p' h
    obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_mul_of_disjoint hdisj p.1.2.1 p'.1.2.1 p.2.2.1 p'.2.2.1
      (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨w, hw, hw2⟩
    obtain ⟨x, hx, k, hk, rfl⟩ := hgen w hw
    rw [Commute.mul_pow (hcomm x hx k hk) 2] at hw2
    obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_mul_of_disjoint hdisj (R.pow_mem hx 2) hx₀
      (T.pow_mem hk 2) hk₀ hw2
    exact ⟨⟨⟨x, hx, h1⟩, ⟨k, hk, h2⟩⟩, rfl⟩

theorem involution_cases_of_internal_prod (hcomm : ∀ x ∈ R, ∀ k ∈ T, x * k = k * x)
    (hdisj : ∀ g ∈ R, g ∈ T → g = 1) (hgen : ∀ w ∈ P, ∃ x ∈ R, ∃ k ∈ T, x * k = w) {z : X}
    (hTinv : ∀ k ∈ T, k ^ 2 = 1 → k = 1 ∨ k = z) {w : X} (hw : w ∈ P) (hw2 : w ^ 2 = 1)
    (hw1 : w ≠ 1) :
    w = z ∨ (w ∈ R ∧ w ^ 2 = 1 ∧ w ≠ 1) ∨ ∃ x, (x ∈ R ∧ x ^ 2 = 1 ∧ x ≠ 1) ∧ x * z = w := by
  obtain ⟨x, hx, k, hk, rfl⟩ := hgen w hw
  rw [Commute.mul_pow (hcomm x hx k hk) 2, ← mul_one 1] at hw2
  obtain ⟨hx2, hk2⟩ := eq_and_eq_of_mul_eq_mul_of_disjoint hdisj (R.pow_mem hx 2) R.one_mem
    (T.pow_mem hk 2) T.one_mem hw2
  rcases hTinv k hk hk2 with rfl | rfl
  · rw [mul_one] at hw1 ⊢
    exact Or.inr (Or.inl ⟨hx, hx2, hw1⟩)
  · by_cases hx1 : x = 1
    · subst hx1
      exact Or.inl (one_mul _)
    · exact Or.inr (Or.inr ⟨x, ⟨hx, hx2, hx1⟩, rfl⟩)

end Product

theorem eq_or_eq_of_card_subtype_eq_two {α : Type*} {p : α → Prop}
    (h : Nat.card {a // p a} = 2) {x y w : α} (hx : p x) (hy : p y) (hxy : x ≠ y) (hw : p w) :
    w = x ∨ w = y := by
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (⟨x, hx⟩ : {a // p a})).mp h
  by_cases hwx : w = x
  · exact Or.inl hwx
  · right
    have h1 := hu ⟨w, hw⟩ (fun h' => hwx (congrArg Subtype.val h'))
    have h2 := hu ⟨y, hy⟩ (fun h' => hxy (congrArg Subtype.val h').symm)
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_central_sq_eq_of_card_sq_eq_two {T : Subgroup X} (hT : IsPGroup 2 T) {z : X}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hTinv : ∀ k ∈ T, k ^ 2 = 1 → k = 1 ∨ k = z)
    (hcard : Nat.card {k : X // k ∈ T ∧ k ^ 2 = z} = 2) :
    ∃ k ∈ T, k ^ 2 = z ∧ ∀ t ∈ T, t * k = k * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨k, hkT, hk2⟩⟩ := (Nat.card_pos_iff.mp (by rw [hcard]; norm_num)).1
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2])
  have hki2 : k⁻¹ ^ 2 = z := by rw [inv_pow, hk2, hzz]
  have hkk : k ≠ k⁻¹ := by
    intro h
    apply hz1
    rw [← hk2, pow_two]
    nth_rw 2 [h]
    exact mul_inv_cancel k
  refine ⟨k, hkT, hk2, fun t ht => ?_⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨t, ht⟩
  rw [Subgroup.orderOf_mk] at ha
  rcases a with _ | _ | a
  · rw [pow_zero, orderOf_eq_one_iff] at ha
    rw [ha, one_mul, mul_one]
  · have ht2 : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ha, zero_add, pow_one] at h
    rcases hTinv t ht ht2 with rfl | rfl
    · rw [one_mul, mul_one]
    · rw [← hk2, pow_two, mul_assoc]
  · set s := t ^ 2 ^ a
    have hdvd : 2 ^ a ∣ orderOf t := ha ▸ pow_dvd_pow 2 (by omega)
    have hs4 : orderOf s = 4 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, ha, show a + 1 + 1 = a + 2 by ring, pow_add,
        Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
      norm_num
    have hs2 : orderOf (s ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs4]; norm_num), hs4]
    have hsT : s ∈ T := T.pow_mem ht _
    have hss : s ^ 2 = z := by
      have h4 := pow_orderOf_eq_one (s ^ 2)
      rw [hs2] at h4
      rcases hTinv (s ^ 2) (T.pow_mem hsT 2) h4 with h | h
      · rw [h, orderOf_one] at hs2
        exact absurd hs2 (by norm_num)
      · exact h
    have hts : Commute t s := (Commute.refl t).pow_right _
    rcases eq_or_eq_of_card_subtype_eq_two (p := fun k => k ∈ T ∧ k ^ 2 = z) hcard
      ⟨hkT, hk2⟩ ⟨T.inv_mem hkT, hki2⟩ hkk ⟨hsT, hss⟩ with h | h
    · rw [← h]
      exact hts.eq
    · have h' : k = s⁻¹ := by rw [h, inv_inv]
      rw [h']
      exact hts.inv_right.eq

omit [Group X] in
theorem exists_mem_of_odd_card_of_parity [Finite X] {A B C : Set X} {z : X} (hA : Odd (Nat.card A))
    (hB : Even (Nat.card B + 1)) (hzB : z ∉ B) (hsub : ∀ w ∈ A, w = z ∨ w ∈ B ∨ w ∈ C)
    (hzA : z ∈ A) (hBA : B ⊆ A) : ∃ c ∈ C, c ∈ A := by
  by_contra h
  push Not at h
  have hAB : A = insert z B := by
    refine Set.Subset.antisymm (fun w hw => ?_) (Set.insert_subset hzA hBA)
    rcases hsub w hw with rfl | hwB | hwC
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ hwB
    · exact absurd hw (h w hwC)
  rw [hAB, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hzB (Set.toFinite B),
    ← Nat.card_coe_set_eq] at hA
  exact (Nat.not_even_iff_odd.mpr hA) hB

end CFSG.ProperTwoGeneratedCore.Lemma37
