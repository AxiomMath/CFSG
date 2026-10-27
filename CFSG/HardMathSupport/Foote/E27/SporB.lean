module

public import CFSG.HardMathSupport.Foote.E27.SporSpecial
public import CFSG.Sporadic.Bridge.BOrder

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Blueprint CFSG.Monster.B.Pinned Subgroup

section Certificates


theorem factorization_card_nativeB :
    (Nat.card NativeSporadic.B).factorization 3 = 13 := by
  have h2 : CFSG.Open.monsterBabyOrder =
      3 ^ 13 * (2 ^ 41 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47) := by
    unfold CFSG.Open.monsterBabyOrder
    ring
  rw [CFSG.Monster.Existence.card_nativeB, h2, Nat.factorization_mul (by positivity)
    (by positivity), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem three_pow_thirteen_dvd_card_LThree :
    3 ^ 13 ∣ Nat.card LThree := by
  have := finite_B
  have h1 : Nat.card rhoThree.ker * Nat.card rhoThree.range = Nat.card LThree := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : 3 ^ 9 ∣ Nat.card rhoThree.ker := by
    have := Subgroup.card_dvd_of_le QThree_le_ker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QThree_le_LThree).toEquiv,
      card_QThree] at this
  have h3 : 3 ^ 4 ∣ Nat.card rhoThree.range := by
    rw [range_rhoThree]
    exact CFSG.Sporadic.Bridge.B.three_four_dvd_card_KThree
  rw [← h1, show (3 : ℕ) ^ 13 = 3 ^ 9 * 3 ^ 4 by norm_num]
  exact Nat.mul_dvd_mul h2 h3

theorem e27_not_B
    (hbr : Nonempty (NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.B).Group))
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z)
    (hz : z ∈ K)
    (e : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.B).Group)) :
    False := by
  have hfin := finite_B
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQcard, hcen, hcomm, hzcard, ⟨_, eQ, -, -⟩, hQL, hQLn, -⟩ :=
    pinned_B_three_power_twelve_divisibility
  have hzQ : zpowers zThree ≤ QThree := (zpowers_le (G := NativeSporadic.B)).mpr zThree_mem
  refine @E27Config.false_of_normal_special X _ _ K R T z hc hz NativeSporadic.B inferInstance
    hfin (e.some.trans hbr.some.symm) QThree LThree 4 le_rfl hQcard ?_ ?_ ?_ ?_ ?_
  · rw [hcen, ← hzcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hzQ).toEquiv
  · intro x y
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ commutator QThree :=
      commutator_mem_commutator (mem_top x) (mem_top y)
    rwa [hcomm, ← hcen] at hxy
  · intro x
    rw [hcen, ← QuotientGroup.eq_one_iff]
    apply eQ.injective
    rw [QuotientGroup.mk_pow, map_pow, map_one]
    have h3 : ∀ v : Multiplicative (Fin 8 → ZMod 3), v ^ 3 = 1 := fun v => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    exact h3 _
  · exact le_normalizer_of_normal_subgroupOf (hK := hQLn) hQL
  · rw [factorization_card_nativeB]
    exact three_pow_thirteen_dvd_card_LThree

end Certificates

end CFSG.HardMathSupport.Foote.E27
