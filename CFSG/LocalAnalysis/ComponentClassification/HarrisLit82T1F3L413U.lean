module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.L413

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type*} [Field K]

theorem transvection_pow_three (h3 : (3 : K) = 0) {i j : Fin 2} (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c ^ 3 = 1 := by
  have hmul : ∀ a b : K, Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij b =
        Matrix.SpecialLinearGroup.transvection hij (a + b) := fun a b =>
    Subtype.ext (Matrix.transvection_mul_transvection_same _ _ hij a b)
  rw [pow_three, hmul, hmul, show c + (c + c) = 3 * c by ring, h3, zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

variable [Finite K] {G : Type*} [Group G] [Finite G]

theorem range_eq_of_normal {ι : Type*} (hodd : Odd (Nat.card K)) (h3K : 3 ≤ Nat.card K)
    (h3 : (3 : K) = 0) (S : ι → Subgroup G) (z : ι → G) (C : Subgroup G)
    (hSC : ∀ i, S i ≤ C) (hCN : ∀ i, C ≤ Subgroup.normalizer (S i : Set G))
    (eS : ∀ i, Nonempty (↥(S i) ≃* SL(2, K))) (hzS : ∀ i, z i ∈ S i)
    (hz2 : ∀ i, orderOf (z i) = 2) (hzinj : Function.Injective z)
    (hZ : ∀ j (y : G), y ^ 3 = 1 → (∀ k, k ≠ j → ∀ s ∈ S k, y * s = s * y) → y ∈ S j)
    {φ : SL(2, K) →* G} (hφ : Function.Injective φ) (hAC : φ.range ≤ C)
    (hCA : C ≤ Subgroup.normalizer (φ.range : Set G)) {j : ι} (hzA : z j ∈ φ.range) :
    φ.range = S j := by
  have hinvA : ∀ t ∈ φ.range, orderOf t = 2 → t = z j := by
    have key : ∀ t ∈ φ.range, orderOf t = 2 → t = φ (-1) := by
      rintro _ ⟨M, rfl⟩ hM
      rw [orderOf_injective φ hφ M, sl2_orderOf_eq_two_iff hodd] at hM
      rw [hM]
    intro t ht ht2
    rw [key t ht ht2, key (z j) hzA (hz2 j)]
  have hinvS : ∀ k, ∀ t ∈ S k, orderOf t = 2 → t = z k := by
    intro k t ht ht2
    obtain ⟨e⟩ := eS k
    have h1 : (⟨t, ht⟩ : S k) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rwa [Subgroup.orderOf_mk])
    have h2 : (⟨z k, hzS k⟩ : S k) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk]; exact hz2 k)
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hcomm : ∀ k, k ≠ j → ∀ a ∈ φ.range, ∀ s ∈ S k, a * s = s * a := by
    intro k hk a ha s hs
    obtain ⟨e⟩ := eS k
    have hRS : ∀ s' ∈ S k, ∀ n ∈ φ.range, s' * n * s'⁻¹ ∈ φ.range := fun s' hs' n hn =>
      (Subgroup.mem_normalizer_iff.mp (hCA (hSC k hs')) n).mp hn
    have hSR : ∀ a' ∈ φ.range, ∀ n ∈ S k, a' * n * a'⁻¹ ∈ S k := fun a' ha' n hn =>
      (Subgroup.mem_normalizer_iff.mp (hCN k (hAC ha')) n).mp hn
    set N := (φ.range ⊓ S k).subgroupOf (S k) with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hRS g g.2 n hn.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hn.2)
        (Subgroup.inv_mem _ g.2)⟩
    have hNodd : Odd (Nat.card N) := by
      rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => ?_)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have ht' : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
      exact hk (hzinj ((hinvS k t t.2.2 ht').symm.trans (hinvA t t.2.1 ht')))
    have hbot := normal_odd_of_equiv_sl2 hodd h3K e N hNn hNodd
    have hw : a * s * a⁻¹ * s⁻¹ ∈ φ.range ⊓ S k := by
      refine ⟨?_, Subgroup.mul_mem _ (hSR a ha s hs) (Subgroup.inv_mem _ hs)⟩
      rw [show a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) by group]
      exact Subgroup.mul_mem _ ha (hRS s hs _ (Subgroup.inv_mem _ ha))
    have hw1 : (⟨a * s * a⁻¹ * s⁻¹, hw.2⟩ : S k) ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact hw
    rw [hbot, Subgroup.mem_bot] at hw1
    have h1 : a * s * a⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hw1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hle : φ.range ≤ S j := by
    have hgen : ∀ {i' j' : Fin 2} (hij : i' ≠ j') (c : K),
        φ (Matrix.SpecialLinearGroup.transvection hij c) ∈ S j := fun hij c =>
      hZ j _ (by rw [← map_pow, transvection_pow_three h3, map_one])
        (fun k hk s hs => hcomm k hk _ ⟨_, rfl⟩ s hs)
    rintro _ ⟨M, rfl⟩
    exact Frame.sl2_apply_mem φ (S j) (hgen _) (hgen _) M
  obtain ⟨e⟩ := eS j
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]

end CFSG.ComponentClassification.HarrisLit.T1.L413
