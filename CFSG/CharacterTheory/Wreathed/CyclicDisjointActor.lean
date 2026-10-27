module

public import CFSG.CharacterTheory.Wreathed.CyclicDisjointActorSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Wreathed.CyclicDisjointActor

open CFSG.Wreathed.Original
open scoped Pointwise

theorem maximal_cyclic_disjoint_actor_forces_cyclic_kernel_or_full_wreath (n : ℕ) (hn : 2 ≤ n)
    (A X : Subgroup (Wreath (2 ^ n))) (hAc : IsCyclic A) (hAcard : Nat.card A = 2 ^ n)
    (hAX : A ≤ Subgroup.normalizer (X : Set (Wreath (2 ^ n)))) (hXA : X ⊓ A = ⊥) :
    IsCyclic X ∨ ((X : Set (Wreath (2 ^ n))) * (A : Set (Wreath (2 ^ n))) = Set.univ ∧
      X ⊔ A = ⊤ ∧ Nat.card X = 2 * 2 ^ n ∧ A ≤ U (2 ^ n) ∧
      ∀ i j : ℤ, Subgroup.zpowers (s (2 ^ n) ^ i * t (2 ^ n) ^ j) = A → (i + j) % 2 = 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstr : OriginalStructure (2 ^ (k + 1)) :=
    wreath_center_involution_and_quaternion_coordinates (k + 1) hn
  by_cases hXc : IsCyclic X
  · exact Or.inl hXc
  right
  have hxX := x_mem_of_not_isCyclic hk X hXc
  have hx1 : x (2 ^ (k + 1)) ≠ 1 := by
    intro h
    have h1 := hstr.involution_orders.1
    rw [h, orderOf_one] at h1
    omega
  have hxA : x (2 ^ (k + 1)) ∉ A := fun h => hx1 (by
    have hmem : x (2 ^ (k + 1)) ∈ X ⊓ A := ⟨hxX, h⟩
    rwa [hXA, Subgroup.mem_bot] at hmem)
  obtain ⟨g, hg⟩ : ∃ g : Wreath (2 ^ (k + 1)), Subgroup.zpowers g = A := by
    obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
    refine ⟨a, le_antisymm (Subgroup.zpowers_le.mpr a.2) fun y hy => ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ha ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
  have hgord : orderOf g = 2 ^ (k + 1) := by rw [← Nat.card_zpowers, hg, hAcard]
  have hgU : g ∈ U (2 ^ (k + 1)) := by
    by_contra hgU
    obtain ⟨p, q, e, rfl⟩ := exists_element g
    rw [U_eq, element_mem_base] at hgU
    have he : e = 1 := (swap_exponent_cases e).resolve_left hgU
    subst he
    apply hxA
    rw [← hg]
    have hsq : element (2 ^ (k + 1)) p q 1 ^ 2 ∈ Subgroup.center (Wreath (2 ^ (k + 1))) := by
      rw [element_swap_sq, element_mem_center_iff _ (one_lt_modulus k)]
      exact ⟨rfl, rfl⟩
    have hsq1 : element (2 ^ (k + 1)) p q 1 ^ 2 ≠ 1 := by
      intro h
      have h1 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h)
      rw [hgord] at h1
      have h2 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      (x_mem_zpowers_of_mem_center hsq hsq1)
  have hAU : A ≤ U (2 ^ (k + 1)) := hg ▸ Subgroup.zpowers_le.mpr hgU
  have hpar : ∀ i j : ℤ, Subgroup.zpowers (s (2 ^ (k + 1)) ^ i * t (2 ^ (k + 1)) ^ j) = A →
      (i + j) % 2 = 1 := by
    intro i j hij
    have hcoord : s (2 ^ (k + 1)) ^ i * t (2 ^ (k + 1)) ^ j =
        element (2 ^ (k + 1)) (i : ZMod (2 ^ (k + 1))) (j : ZMod (2 ^ (k + 1))) 0 := by
      rw [s, t, element_base_zpow, element_base_zpow, element_base_mul]
      simp only [zsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    rw [hcoord] at hij
    have hord : orderOf (element (2 ^ (k + 1)) (i : ZMod (2 ^ (k + 1)))
        (j : ZMod (2 ^ (k + 1))) 0) = 2 ^ (k + 1) := by
      rw [← Nat.card_zpowers, hij, hAcard]
    have h := parity_of_generator hord (hij ▸ hxA)
    rw [map_intCast, map_intCast, ← Int.cast_add, ← Int.cast_one,
      ZMod.intCast_eq_intCast_iff'] at h
    omega
  have hXU : ¬ X ≤ U (2 ^ (k + 1)) := by
    intro hXU
    have habel : ∀ u v : X, u * v = v * u := by
      intro u v
      have h := congrArg Subtype.val
        ((isMulCommutative_iff.mp hstr.base_abelian) ⟨u, hXU u.2⟩ ⟨v, hXU v.2⟩)
      exact Subtype.ext h
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := habel }
    have hX2 : IsPGroup 2 X := (wreath_isPGroup k).to_subgroup X
    obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hX2
    have hnu : ¬ ∀ u v : X, orderOf u = 2 → orderOf v = 2 → u = v := fun h =>
      hXc (TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
        e X hX2 he h)
    simp only [not_forall] at hnu
    obtain ⟨u, v, hu, hv, huv⟩ := hnu
    obtain ⟨h1, h2, h3⟩ := three_involutions_mem X u.2 v.2 (hXU u.2) (hXU v.2)
      (by rwa [Subgroup.orderOf_coe]) (by rwa [Subgroup.orderOf_coe])
      (fun h => huv (Subtype.ext h))
    have hwo : orderOf (g ^ 2 ^ k) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hgord]; exact pow_dvd_pow 2 (by omega)), hgord,
        Nat.pow_div (by omega) two_pos, show k + 1 - k = 1 by omega, pow_one]
    have hwX : g ^ 2 ^ k ∈ X := by
      rcases involution_of_mem_base (Subgroup.pow_mem _ hgU _) hwo with h | h | h <;> rw [h] <;>
        assumption
    have hwA : g ^ 2 ^ k ∈ A := hg ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _
    have hmem : g ^ 2 ^ k ∈ X ⊓ A := ⟨hwX, hwA⟩
    rw [hXA, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hwo
    omega
  obtain ⟨b, hbX, hbU⟩ := Set.not_subset.mp hXU
  obtain ⟨p, q, eb, rfl⟩ := exists_element b
  rw [U_eq, SetLike.mem_coe, element_mem_base] at hbU
  have heb : eb = 1 := (swap_exponent_cases eb).resolve_left hbU
  subst heb
  obtain ⟨i, j, eg, rfl⟩ := exists_element g
  rw [U_eq, element_mem_base] at hgU
  subst hgU
  have hpij := parity_of_generator hgord (hg ▸ hxA)
  have hcX : element (2 ^ (k + 1)) (i - j) (j - i) 0 ∈ X := by
    rw [← commutator_base_swap i j p q]
    have hgN := hAX (hg ▸ Subgroup.mem_zpowers _)
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp hbX) (X.inv_mem hbX)
  have hcpar : parity k (i - j) ≠ 0 := parity_sub_ne_zero hpij
  have hcord : orderOf (element (2 ^ (k + 1)) (i - j) (j - i) 0) = 2 ^ (k + 1) := by
    rw [show j - i = -(i - j) by ring]
    exact orderOf_antidiagonal hcpar
  have : (U (2 ^ (k + 1))).Normal := by
    rw [U_eq]
    exact baseSubgroup_normal _
  have hcU : element (2 ^ (k + 1)) (i - j) (j - i) 0 ∈ U (2 ^ (k + 1)) := by
    rw [U_eq, element_mem_base]
  have hUXcard : 2 ^ (k + 1) ≤ Nat.card (U (2 ^ (k + 1)) ⊓ X : Subgroup _) := by
    have h := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr ⟨hcU, hcX⟩ :
      Subgroup.zpowers (element (2 ^ (k + 1)) (i - j) (j - i) 0) ≤ U (2 ^ (k + 1)) ⊓ X)
    rwa [Nat.card_zpowers, hcord] at h
  have hrel : (U (2 ^ (k + 1))).relIndex X = 2 := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := U (2 ^ (k + 1))) (K := X)
    rw [hstr.base_index] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hXU
    · exact h
  have hXcard : 2 * 2 ^ (k + 1) ≤ Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := U (2 ^ (k + 1))) (K := X)
    rw [hrel] at h
    omega
  have hXAcard := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X A hAX
    (disjoint_iff.mpr hXA)
  have hle : Nat.card (X ⊔ A : Subgroup _) ≤ Nat.card (Wreath (2 ^ (k + 1))) :=
    Subgroup.card_le_card_group _
  rw [hXAcard, hAcard, card_wreath, sq, ← mul_assoc] at hle
  have hXeq : Nat.card X = 2 * 2 ^ (k + 1) :=
    le_antisymm (Nat.le_of_mul_le_mul_right hle (by positivity)) hXcard
  have htop : X ⊔ A = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hXAcard, hXeq, hAcard, card_wreath]
    ring
  refine ⟨?_, htop, hXeq, hAU, hpar⟩
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left X A hAX, htop, Subgroup.coe_top]

end CFSG.Wreathed.CyclicDisjointActor
