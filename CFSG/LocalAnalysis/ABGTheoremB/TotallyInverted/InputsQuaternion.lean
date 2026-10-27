module

public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Inputs

open CFSG.Open

structure FourFusionModel {M : Type*} [Group M] (Q : Subgroup M) (x : M) : Prop where
  central : x ∈ Subgroup.center M
  four : ∀ u v : M, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u ≠ v →
    u = x ∨ v = x ∨ u * v = x
  conj : ∀ t : M, orderOf t = 2 → t ≠ x → ∃ y ∈ Q, y * t * y⁻¹ = t * x

theorem orderOf_mul_eq_two {M : Type*} [Group M] {u v : M} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) : orderOf (u * v) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  rw [orderOf_eq_prime_iff]
  refine ⟨by rw [Commute.mul_pow huv, hu2, hv2, one_mul], fun h => hne ?_⟩
  rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)]

theorem FourFusionModel.exists_central_four {M R : Type*} [Group M] [Group R]
    {Q : Subgroup M} {x : M} (hM : FourFusionModel Q x) (ι : R →* M)
    (hι : Function.Injective ι) (Y : Subgroup R) (hY : Y.map ι = Q) (T : Subgroup R)
    (hT : ∀ t ∈ T, t * t = 1) {u v : R} (hu : u ∈ T) (hv : v ∈ T) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) :
    ∃ z ∈ T, z ≠ 1 ∧ z ∈ Subgroup.center R ∧
      ∀ t ∈ T, t ≠ 1 → t ≠ z → ∃ y ∈ Y, y * t * y⁻¹ = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ t ∈ T, t ≠ 1 → orderOf (ι t) = 2 := by
    intro t ht ht1
    rw [orderOf_injective ι hι, orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact hT t ht, ht1⟩
  have hcomm : u * v = v * u := by
    calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right (hT _ (T.mul_mem hu hv))).symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by
        rw [inv_eq_of_mul_eq_one_right (hT u hu), inv_eq_of_mul_eq_one_right (hT v hv)]
  have hz : ∃ z ∈ T, z ≠ 1 ∧ ι z = x := by
    rcases hM.four (ι u) (ι v) (hord u hu hu1) (hord v hv hv1)
        (by rw [← map_mul, ← map_mul, hcomm]) (hι.ne huv) with h | h | h
    · exact ⟨u, hu, hu1, h⟩
    · exact ⟨v, hv, hv1, h⟩
    · refine ⟨u * v, T.mul_mem hu hv, fun h1 => huv ?_, by rw [map_mul]; exact h⟩
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right (hT v hv)]
  obtain ⟨z, hzT, hz1, hzx⟩ := hz
  refine ⟨z, hzT, hz1, Subgroup.mem_center_iff.mpr fun g => hι ?_, fun t ht ht1 htz => ?_⟩
  · rw [map_mul, map_mul, hzx]
    exact Subgroup.mem_center_iff.mp hM.central (ι g)
  · obtain ⟨y, hyQ, hy⟩ := hM.conj (ι t) (hord t ht ht1) (by rw [← hzx]; exact hι.ne htz)
    rw [← hY] at hyQ
    obtain ⟨y', hy'Y, rfl⟩ := hyQ
    refine ⟨y', hy'Y, hι ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, hzx]
    exact hy

theorem sd_fourFusionModel (n : ℕ) (hn : 4 ≤ n) :
    FourFusionModel (Semidihedral.quaternionSubgroup n) (Semidihedral.z n) where
  central := Semidihedral.z_mem_center n hn
  four u v hu hv huv hne := by
    have hn3 : 3 ≤ n := by omega
    obtain ⟨⟨i, e⟩, rfl⟩ := (Semidihedral.coordinateEquiv n hn3).symm.surjective u
    obtain ⟨⟨j, f⟩, rfl⟩ := (Semidihedral.coordinateEquiv n hn3).symm.surjective v
    change orderOf (Semidihedral.element n hn3 i e) = 2 at hu
    change orderOf (Semidihedral.element n hn3 j f) = 2 at hv
    change Semidihedral.element n hn3 i e * Semidihedral.element n hn3 j f =
      Semidihedral.element n hn3 j f * Semidihedral.element n hn3 i e at huv
    change Semidihedral.element n hn3 i e ≠ Semidihedral.element n hn3 j f at hne
    change Semidihedral.element n hn3 i e = Semidihedral.z n ∨
      Semidihedral.element n hn3 j f = Semidihedral.z n ∨
      Semidihedral.element n hn3 i e * Semidihedral.element n hn3 j f = Semidihedral.z n
    rcases Semidihedral.exponent_cases e with rfl | rfl
    · obtain rfl := (Semidihedral.rotation_involution_iff n hn3 i).mp hu
      exact Or.inl (Semidihedral.z_eq_element n hn3).symm
    rcases Semidihedral.exponent_cases f with rfl | rfl
    · obtain rfl := (Semidihedral.rotation_involution_iff n hn3 j).mp hv
      exact Or.inr (Or.inl (Semidihedral.z_eq_element n hn3).symm)
    have h2 := orderOf_mul_eq_two hu hv huv hne
    rw [Semidihedral.element_reflection_mul, show (1 + 1 : ZMod 2) = 0 by decide] at h2 ⊢
    rw [(Semidihedral.rotation_involution_iff n hn3 _).mp h2]
    exact Or.inr (Or.inr (Semidihedral.z_eq_element n hn3).symm)
  conj t ht htz := by
    have hn3 : 3 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    obtain ⟨⟨i, e⟩, rfl⟩ := (Semidihedral.coordinateEquiv _ hn3).symm.surjective t
    change orderOf (Semidihedral.element _ hn3 i e) = 2 at ht
    change Semidihedral.element _ hn3 i e ≠ Semidihedral.z _ at htz
    rcases Semidihedral.exponent_cases e with rfl | rfl
    · obtain rfl := (Semidihedral.rotation_involution_iff _ hn3 i).mp ht
      exact absurd (Semidihedral.z_eq_element _ hn3).symm htz
    refine ⟨Semidihedral.r (k + 4) ^ (2 ^ (k + 1)), ?_, ?_⟩
    · rw [pow_succ', pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
    change Semidihedral.r (k + 4) ^ (2 ^ (k + 1)) * Semidihedral.element _ hn3 i 1 *
      (Semidihedral.r (k + 4) ^ (2 ^ (k + 1)))⁻¹ =
      Semidihedral.element _ hn3 i 1 * Semidihedral.z (k + 4)
    have hm : Semidihedral.modulus (k + 4) = 8 * 2 ^ k := by
      rw [Semidihedral.modulus, show k + 4 - 1 = k + 3 by omega, pow_add]
      norm_num
      ring
    have hh : Semidihedral.half (k + 4) = 4 * 2 ^ k := by
      rw [Semidihedral.half, show k + 4 - 2 = k + 2 by omega, pow_add]
      norm_num
      ring
    have h8 : ((8 * 2 ^ k : ℕ) : ZMod (Semidihedral.modulus (k + 4))) = 0 := by
      rw [← hm]
      exact ZMod.natCast_self _
    push_cast at h8
    rw [mul_inv_eq_iff_eq_mul, Semidihedral.r_pow_eq_element _ hn3,
      Semidihedral.z_eq_element _ hn3, Semidihedral.element_rotation_mul,
      Semidihedral.element_reflection_mul, add_zero, Semidihedral.element_reflection_mul,
      add_zero, Semidihedral.element_eq_iff]
    refine ⟨?_, rfl⟩
    simp only [Semidihedral.twist, hh]
    push_cast
    linear_combination (1 - 3 * (2 : ZMod (Semidihedral.modulus (k + 4))) ^ k) * h8

theorem wreath_half_add_half (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by
  rw [← Nat.cast_add, ← two_mul, ← pow_succ', ZMod.natCast_self]

theorem wreath_fourFusionModel (k : ℕ) (hk : 1 ≤ k) :
    FourFusionModel (Wreathed.Original.Y (2 ^ (k + 1)))
      (Wreathed.element (2 ^ (k + 1)) (2 ^ k : ℕ) (2 ^ k : ℕ) 0) where
  central := by
    have hm : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    exact (Wreathed.element_mem_center_iff _ hm _ _ _).mpr ⟨rfl, rfl⟩
  four u v hu hv huv hne := by
    have hm : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    have hne0 := Wreathed.half_residue_ne_zero k
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (k + 1))).symm.surjective u
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (k + 1))).symm.surjective v
    change orderOf (Wreathed.element _ a b e) = 2 at hu
    change orderOf (Wreathed.element _ c d f) = 2 at hv
    change Wreathed.element _ a b e * Wreathed.element _ c d f =
      Wreathed.element _ c d f * Wreathed.element _ a b e at huv
    change Wreathed.element _ a b e ≠ Wreathed.element _ c d f at hne
    change Wreathed.element _ a b e = _ ∨ Wreathed.element _ c d f = _ ∨
      Wreathed.element _ a b e * Wreathed.element _ c d f = _
    rcases Wreathed.swap_exponent_cases e with rfl | rfl <;>
      rcases Wreathed.swap_exponent_cases f with rfl | rfl
    · rcases (Wreathed.element_base_involution_iff k a b).mp hu with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      all_goals rcases (Wreathed.element_base_involution_iff k c d).mp hv with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact Or.inr (Or.inl rfl)
        | exact absurd rfl hne
        | exact Or.inr (Or.inr (by rw [Wreathed.element_base_mul, zero_add, add_zero]))
    · rw [Wreathed.element_base_mul, Wreathed.element_swap_mul, Wreathed.element_eq_iff] at huv
      obtain rfl : a = b := by linear_combination huv.1
      exact Or.inl (Wreathed.unique_central_involution k _ hu
        ((Wreathed.element_mem_center_iff _ hm a a 0).mpr ⟨rfl, rfl⟩))
    · rw [Wreathed.element_base_mul, Wreathed.element_swap_mul, Wreathed.element_eq_iff] at huv
      obtain rfl : c = d := by linear_combination huv.2.1
      exact Or.inr (Or.inl (Wreathed.unique_central_involution k _ hv
        ((Wreathed.element_mem_center_iff _ hm c c 0).mpr ⟨rfl, rfl⟩)))
    · have h2 := orderOf_mul_eq_two hu hv huv hne
      have hab := (Wreathed.element_swap_involution_iff _ a b).mp hu
      have hcd := (Wreathed.element_swap_involution_iff _ c d).mp hv
      rw [Wreathed.element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide] at h2 ⊢
      rcases (Wreathed.element_base_involution_iff k _ _).mp h2 with
        ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · exact Or.inr (Or.inr (by rw [h1, h1']))
      · exact absurd (by linear_combination -h1 + hab + hcd - h1') hne0
      · exact absurd (by linear_combination -h1' + hab + hcd - h1) hne0
  conj t ht htx := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hhh := wreath_half_add_half (j + 1)
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (j + 1 + 1))).symm.surjective t
    change orderOf (Wreathed.element _ a b e) = 2 at ht
    change Wreathed.element _ a b e ≠ _ at htx
    change ∃ y ∈ Wreathed.Original.Y (2 ^ (j + 1 + 1)),
      y * Wreathed.element _ a b e * y⁻¹ = Wreathed.element _ a b e * _
    rcases Wreathed.swap_exponent_cases e with rfl | rfl
    · refine ⟨Wreathed.Original.d _, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), ?_⟩
      rw [Wreathed.Original.d_eq, Wreathed.conjugate_base_by_swap, Wreathed.element_base_mul]
      rcases (Wreathed.element_base_involution_iff (j + 1) a b).mp ht with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl htx
      · rw [hhh, zero_add]
      · rw [hhh, zero_add]
    · have hab := (Wreathed.element_swap_involution_iff _ a b).mp ht
      refine ⟨Wreathed.Original.r _ ^ (2 ^ j),
        Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _, ?_⟩
      have hq : ((2 ^ (j + 1) : ℕ) : ZMod (2 ^ (j + 1 + 1))) =
          2 * ((2 ^ j : ℕ) : ZMod (2 ^ (j + 1 + 1))) := by
        rw [pow_succ']
        push_cast
        ring
      rw [Wreathed.Original.r_eq, Wreathed.element_base_pow, Wreathed.conjugate_swap_by_base,
        Wreathed.element_swap_mul, add_zero, Wreathed.element_eq_iff]
      refine ⟨?_, ?_, rfl⟩
      · rw [hq, nsmul_eq_mul, nsmul_eq_mul]
        ring
      · rw [nsmul_eq_mul, nsmul_eq_mul]
        linear_combination hq - hhh

end CFSG.ABGTheoremB.TotallyInverted.Inputs
