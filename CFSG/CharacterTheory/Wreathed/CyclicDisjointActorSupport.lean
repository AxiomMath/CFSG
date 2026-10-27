module

public import CFSG.CharacterTheory.Wreathed.BaseOmega
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public section

namespace CFSG.Wreathed.CyclicDisjointActor

open CFSG.Wreathed.Original

noncomputable abbrev parity (k : ℕ) : ZMod (2 ^ (k + 1)) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero k)) (ZMod 2)

theorem one_lt_modulus (k : ℕ) : 1 < 2 ^ (k + 1) :=
  Nat.one_lt_two_pow (Nat.succ_ne_zero k)

theorem x_eq_element (k : ℕ) :
    x (2 ^ (k + 1)) = element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 := by
  rw [x_eq, pow_succ, Nat.mul_div_cancel _ two_pos]

theorem wreath_isPGroup (k : ℕ) : IsPGroup 2 (Wreath (2 ^ (k + 1))) := by
  apply IsPGroup.of_card (n := 2 * (k + 1) + 1)
  rw [card_wreath]
  ring

theorem baseSubgroup_normal (m : ℕ) : (baseSubgroup m).Normal :=
  MonoidHom.normal_ker _

theorem exists_element {m : ℕ} (g : Wreath m) :
    ∃ (u v : ZMod m) (e : ZMod 2), g = element m u v e := by
  obtain ⟨⟨u, v, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  exact ⟨u, v, e, rfl⟩

theorem half_smul_of_parity_ne_zero {k : ℕ} {c : ZMod (2 ^ (k + 1))} (hc : parity k c ≠ 0) :
    (2 ^ k) • c = ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  have h1 : parity k c = 1 := by
    revert hc
    generalize parity k c = d
    revert d
    decide
  have h2 : parity k (c - 1) = 0 := by
    rw [map_sub, h1, map_one]
    decide
  have h3 := (half_two_power_smul_eq_zero_iff (k + 1) (by omega) (c - 1)).mpr h2
  rw [show k + 1 - 1 = k by omega, smul_sub, sub_eq_zero] at h3
  rw [h3, nsmul_eq_mul, mul_one]

theorem half_smul_eq_zero_iff {k : ℕ} (c : ZMod (2 ^ (k + 1))) :
    (2 ^ k) • c = 0 ↔ parity k c = 0 := by
  have h := half_two_power_smul_eq_zero_iff (k + 1) (by omega) c
  rwa [show k + 1 - 1 = k by omega] at h

theorem x_mem_zpowers_of_mem_center {k : ℕ} {g : Wreath (2 ^ (k + 1))}
    (hgc : g ∈ Subgroup.center (Wreath (2 ^ (k + 1)))) (hg1 : g ≠ 1) :
    x (2 ^ (k + 1)) ∈ Subgroup.zpowers g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp (wreath_isPGroup k) g
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hg1 hj
  have hdvd : 2 ^ (j - 1) ∣ orderOf g := by
    rw [hj]
    exact pow_dvd_pow 2 (Nat.sub_le j 1)
  have ho : orderOf (g ^ 2 ^ (j - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hj,
      Nat.pow_div (Nat.sub_le j 1) two_pos, show j - (j - 1) = 1 by omega, pow_one]
  have hc : g ^ 2 ^ (j - 1) ∈ Subgroup.center (Wreath (2 ^ (k + 1))) :=
    Subgroup.pow_mem _ hgc _
  rw [x_eq_element, ← unique_central_involution k _ ho hc]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _

theorem involution_of_mem_base {k : ℕ} {g : Wreath (2 ^ (k + 1))}
    (hg : g ∈ U (2 ^ (k + 1))) (ho : orderOf g = 2) :
    g = element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 ∨
      g = element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0 ∨ g = element (2 ^ (k + 1)) 0 (2 ^ k : ℕ) 0 := by
  obtain ⟨p, q, e, rfl⟩ := exists_element g
  rw [U_eq, element_mem_base] at hg
  subst hg
  rcases (element_base_involution_iff k p q).mp ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem half_add_half (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by
  rw [← Nat.cast_add, ← two_mul, ← pow_succ', ZMod.natCast_self]

theorem three_involutions_mem {k : ℕ} (X : Subgroup (Wreath (2 ^ (k + 1))))
    {u v : Wreath (2 ^ (k + 1))} (hu : u ∈ X) (hv : v ∈ X) (huU : u ∈ U (2 ^ (k + 1)))
    (hvU : v ∈ U (2 ^ (k + 1))) (huo : orderOf u = 2) (hvo : orderOf v = 2) (huv : u ≠ v) :
    element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 ∈ X ∧
      element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0 ∈ X ∧ element (2 ^ (k + 1)) 0 (2 ^ k : ℕ) 0 ∈ X := by
  have hh := half_add_half k
  have hxy : element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 *
      element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0 = element (2 ^ (k + 1)) 0 (2 ^ k : ℕ) 0 := by
    rw [element_base_mul, hh, add_zero]
  have hxy' : element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 *
      element (2 ^ (k + 1)) 0 (2 ^ k : ℕ) 0 = element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0 := by
    rw [element_base_mul, hh, add_zero]
  have hyy' : element (2 ^ (k + 1)) (2 ^ k : ℕ) 0 0 * element (2 ^ (k + 1)) 0 (2 ^ k : ℕ) 0 =
      element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0 := by
    rw [element_base_mul, add_zero, zero_add]
  have hcomm : ∀ a b c d : ZMod (2 ^ (k + 1)),
      element (2 ^ (k + 1)) a b 0 * element (2 ^ (k + 1)) c d 0 =
        element (2 ^ (k + 1)) c d 0 * element (2 ^ (k + 1)) a b 0 := by
    intro a b c d
    rw [element_base_mul, element_base_mul, add_comm a c, add_comm b d]
  rcases involution_of_mem_base huU huo with rfl | rfl | rfl <;>
    rcases involution_of_mem_base hvU hvo with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact ⟨hu, hv, hxy ▸ X.mul_mem hu hv⟩
  · exact ⟨hu, hxy' ▸ X.mul_mem hu hv, hv⟩
  · exact ⟨hv, hu, hxy ▸ (hcomm _ _ _ _) ▸ X.mul_mem hu hv⟩
  · exact absurd rfl huv
  · exact ⟨hyy' ▸ X.mul_mem hu hv, hu, hv⟩
  · exact ⟨hv, hxy' ▸ (hcomm _ _ _ _) ▸ X.mul_mem hu hv, hu⟩
  · exact ⟨hyy' ▸ (hcomm _ _ _ _) ▸ X.mul_mem hu hv, hv, hu⟩
  · exact absurd rfl huv

theorem x_mem_of_not_isCyclic {k : ℕ} (hk : 1 ≤ k) (X : Subgroup (Wreath (2 ^ (k + 1))))
    (hX : ¬ IsCyclic X) : x (2 ^ (k + 1)) ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstr : OriginalStructure (2 ^ (k + 1)) :=
    wreath_center_involution_and_quaternion_coordinates (k + 1) (by omega)
  have hX2 : IsPGroup 2 X := (wreath_isPGroup k).to_subgroup X
  have hcentral : ∀ c ∈ X, c ∈ Subgroup.center (Wreath (2 ^ (k + 1))) → c ≠ 1 →
      x (2 ^ (k + 1)) ∈ X := fun c hcX hcc hc1 =>
    Subgroup.zpowers_le.mpr hcX (x_mem_zpowers_of_mem_center hcc hc1)
  by_cases habel : ∀ u v : X, u * v = v * u
  · by_cases hXU : X ≤ U (2 ^ (k + 1))
    ·
      let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := habel }
      obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hX2
      have hnu : ¬ ∀ u v : X, orderOf u = 2 → orderOf v = 2 → u = v := fun h =>
        hX (TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
          e X hX2 he h)
      simp only [not_forall] at hnu
      obtain ⟨u, v, hu, hv, huv⟩ := hnu
      have huv' : (u : Wreath (2 ^ (k + 1))) ≠ v := fun h => huv (Subtype.ext h)
      rw [x_eq_element]
      exact (three_involutions_mem X u.2 v.2 (hXU u.2) (hXU v.2)
        (by rwa [Subgroup.orderOf_coe]) (by rwa [Subgroup.orderOf_coe]) huv').1
    · obtain ⟨b, hbX, hbU⟩ := Set.not_subset.mp hXU
      obtain ⟨p, q, eb, rfl⟩ := exists_element b
      rw [U_eq, SetLike.mem_coe, element_mem_base] at hbU
      have heb : eb = 1 := by
        rcases swap_exponent_cases eb with h | h
        · exact absurd h hbU
        · exact h
      subst heb
      have hXUc : ∀ c ∈ X, c ∈ U (2 ^ (k + 1)) → c ∈ Subgroup.center (Wreath (2 ^ (k + 1))) := by
        intro c hcX hcU
        obtain ⟨c₁, c₂, ec, rfl⟩ := exists_element c
        rw [U_eq, element_mem_base] at hcU
        subst hcU
        have h := congrArg Subtype.val (habel ⟨_, hcX⟩ ⟨_, hbX⟩)
        change element (2 ^ (k + 1)) c₁ c₂ 0 * element (2 ^ (k + 1)) p q 1 =
          element (2 ^ (k + 1)) p q 1 * element (2 ^ (k + 1)) c₁ c₂ 0 at h
        rw [element_base_mul, element_swap_mul, element_eq_iff] at h
        rw [element_mem_center_iff _ (one_lt_modulus k)]
        refine ⟨rfl, ?_⟩
        have h1 := h.1
        rw [add_comm p c₂] at h1
        exact add_right_cancel h1
      by_cases hnt : ∃ c ∈ X, c ∈ U (2 ^ (k + 1)) ∧ c ≠ 1
      · obtain ⟨c, hcX, hcU, hc1⟩ := hnt
        exact hcentral c hcX (hXUc c hcX hcU) hc1
      · exfalso
        apply hX
        simp only [not_exists, not_and, not_not] at hnt
        have hbot : U (2 ^ (k + 1)) ⊓ X = ⊥ := by
          rw [eq_bot_iff]
          rintro c ⟨hcU, hcX⟩
          exact Subgroup.mem_bot.mpr (hnt c hcX hcU)
        have : (U (2 ^ (k + 1))).Normal := by
          rw [U_eq]
          exact baseSubgroup_normal _
        have hrel : (U (2 ^ (k + 1))).relIndex X ∣ 2 := by
          have h1 := Subgroup.relIndex_dvd_index_of_normal (H := U (2 ^ (k + 1))) (K := X)
          rwa [hstr.base_index] at h1
        have hcard := Subgroup.relIndex_mul_card (H := U (2 ^ (k + 1))) (K := X)
        rw [hbot, Subgroup.card_bot, mul_one] at hcard
        rw [hcard] at hrel
        rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
        · have : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h1).1
          exact isCyclic_of_subsingleton
        · exact isCyclic_of_prime_card (p := 2) h2
  ·
    simp only [not_forall] at habel
    obtain ⟨u, v, huv⟩ := habel
    obtain ⟨-, hZ⟩ := hstr.nonabelian_centralizers X ⟨u, v, huv⟩
    have : Nontrivial X := ⟨⟨u * v, v * u, huv⟩⟩
    have := hX2.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center X)
    have hcmem : ((c : X) : Wreath (2 ^ (k + 1))) ∈ X ⊓ Z (2 ^ (k + 1)) := by
      rw [← hZ]
      exact ⟨c, c.2, rfl⟩
    apply hcentral _ hcmem.1
    · rw [hstr.center]
      exact hcmem.2
    · intro h
      apply hc
      apply Subtype.ext
      exact Subtype.ext h

theorem parity_of_generator {k : ℕ} {i j : ZMod (2 ^ (k + 1))}
    (hord : orderOf (element (2 ^ (k + 1)) i j 0) = 2 ^ (k + 1))
    (hx : x (2 ^ (k + 1)) ∉ Subgroup.zpowers (element (2 ^ (k + 1)) i j 0)) :
    parity k i + parity k j = 1 := by
  have hpow : element (2 ^ (k + 1)) i j 0 ^ (2 ^ k) =
      element (2 ^ (k + 1)) ((2 ^ k) • i) ((2 ^ k) • j) 0 := element_base_pow _ _ _ _
  by_cases hi : parity k i = 0 <;> by_cases hj : parity k j = 0
  · exfalso
    have h1 : element (2 ^ (k + 1)) i j 0 ^ (2 ^ k) = 1 := by
      rw [hpow, (half_smul_eq_zero_iff i).mpr hi, (half_smul_eq_zero_iff j).mpr hj, element_zero]
    have h2 := Nat.le_of_dvd (by positivity) (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [hi, zero_add]
    revert hj
    generalize parity k j = d
    revert d
    decide
  · rw [hj, add_zero]
    revert hi
    generalize parity k i = d
    revert d
    decide
  · exfalso
    apply hx
    have hgx : element (2 ^ (k + 1)) i j 0 ^ (2 ^ k) = x (2 ^ (k + 1)) := by
      rw [hpow, half_smul_of_parity_ne_zero hi, half_smul_of_parity_ne_zero hj, x_eq_element]
    rw [← hgx]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem parity_sub_ne_zero {k : ℕ} {i j : ZMod (2 ^ (k + 1))}
    (h : parity k i + parity k j = 1) : parity k (i - j) ≠ 0 := by
  have key : ∀ a c : ZMod 2, a + c = 1 → a - c ≠ 0 := by decide
  rw [map_sub]
  exact key _ _ h

theorem commutator_base_swap {m : ℕ} (i j p q : ZMod m) :
    element m i j 0 * element m p q 1 * (element m i j 0)⁻¹ * (element m p q 1)⁻¹ =
      element m (i - j) (j - i) 0 := by
  rw [conjugate_swap_by_base, element_swap_inv, element_swap_mul,
    show (1 + 1 : ZMod 2) = 0 by decide, element_eq_iff]
  refine ⟨by ring, by ring, rfl⟩

theorem orderOf_antidiagonal {k : ℕ} {c : ZMod (2 ^ (k + 1))} (hc : parity k c ≠ 0) :
    orderOf (element (2 ^ (k + 1)) c (-c) 0) = 2 ^ (k + 1) := by
  have hdvd : orderOf (element (2 ^ (k + 1)) c (-c) 0) ∣ 2 ^ (k + 1) :=
    orderOf_dvd_of_pow_eq_one (element_base_pow_modulus _ _ _)
  obtain ⟨e, he, hoe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hne
  have hek : e ≤ k := by
    by_contra h
    apply hne
    rw [hoe, show e = k + 1 by omega]
  have h1 : element (2 ^ (k + 1)) c (-c) 0 ^ (2 ^ k) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hoe ▸ pow_dvd_pow 2 hek)
  rw [element_base_pow, element_base_eq_one_iff] at h1
  exact hc ((half_smul_eq_zero_iff c).mp h1.1)

end CFSG.Wreathed.CyclicDisjointActor
