module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartOne.Mult.PPart
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup

theorem three_le_card_of_ne {G : Type*} [Group G] [Finite G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card H := by
  classical
  have := Fintype.ofFinite H
  have hcard : ({⟨1, one_mem H⟩, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact fun h => ha1 (congrArg Subtype.val h).symm
    · exact fun h => hb1 (congrArg Subtype.val h).symm
    · exact fun h => hab (congrArg Subtype.val h)
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact Finset.card_le_univ _

theorem exists_twoCover_quotient {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {u v : Q} (hu : u ∈ center Q) (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    ∃ (N : Subgroup Q) (_ : N.Normal), N ≤ center Q ∧ ¬ 2 ∣ Nat.card N ∧
      IsQuasisimple (Q ⧸ N) ∧ IsPGroup 2 (center (Q ⧸ N)) ∧
      Nonempty ((Q ⧸ N) ⧸ center (Q ⧸ N) ≃* Q ⧸ center Q) ∧
      ∃ u' ∈ center (Q ⧸ N), ∃ v' ∈ center (Q ⧸ N), u' * u' = 1 ∧ v' * v' = 1 ∧ u' ≠ 1 ∧
        v' ≠ 1 ∧ u' ≠ v' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNZ, hN2, hNpow⟩ := RankThree.PartOne.Mult.exists_central_p_complement (K := Q) 2
  have hNn : N.Normal := normal_of_le_center hNZ
  obtain ⟨hQN, -, hcen⟩ := LocalCores.quasisimple_central_quotient hQ N hNZ
  have hnot : ∀ w : Q, w * w = 1 → w ≠ 1 → w ∉ N := by
    intro w hw2 hw1 hwN
    have ho : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
    apply hN2
    have : orderOf (⟨w, hwN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk, ho]
    rw [← this]
    exact orderOf_dvd_natCard _
  refine ⟨N, hNn, hNZ, hN2, hQN, ?_, ⟨?_⟩, (u : Q ⧸ N), ?_, (v : Q ⧸ N), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [hcen] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hNpow z hz
    refine ⟨k, Subtype.ext ?_⟩
    change ((QuotientGroup.mk' N) z) ^ 2 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  · exact (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient N (center Q) hNZ)
  · rw [hcen]; exact ⟨u, hu, rfl⟩
  · rw [hcen]; exact ⟨v, hv, rfl⟩
  · rw [← QuotientGroup.mk_mul, hu2]; rfl
  · rw [← QuotientGroup.mk_mul, hv2]; rfl
  · intro h
    exact hnot u hu2 hu1 ((QuotientGroup.eq_one_iff u).mp h)
  · intro h
    exact hnot v hv2 hv1 ((QuotientGroup.eq_one_iff v).mp h)
  · intro h
    rw [QuotientGroup.eq] at h
    have hc : u⁻¹ * v = v * u⁻¹ := mem_center_iff.mp hv u⁻¹
    refine hnot (u⁻¹ * v) ?_ ?_ h
    · calc u⁻¹ * v * (u⁻¹ * v) = u⁻¹ * (v * u⁻¹) * v := by group
        _ = u⁻¹ * (u⁻¹ * v) * v := by rw [hc]
        _ = (u * u)⁻¹ * (v * v) := by group
        _ = 1 := by rw [hu2, hv2, inv_one, one_mul]
    · intro h1
      apply huv
      calc u = u * (u⁻¹ * v) := by rw [h1, mul_one]
        _ = v := by group

theorem exists_noncentral_involution_of_quotient {Q : Type} [Group Q] [Finite Q]
    {N : Subgroup Q} [N.Normal] (hN2 : ¬ 2 ∣ Nat.card N) {y : Q ⧸ N} (hy2 : y * y = 1)
    (hyZ : y ∉ center (Q ⧸ N)) : ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hx₀N : x₀ * x₀ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hy2
  set r := orderOf (x₀ * x₀) with hr
  have hrodd : ¬ 2 ∣ r := fun h => hN2 (h.trans (by
    rw [hr, ← Subgroup.orderOf_mk (x₀ * x₀) hx₀N]
    exact orderOf_dvd_natCard _))
  obtain ⟨k, hk⟩ : Odd r := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hrodd)
  have hx2 : x₀ ^ r * x₀ ^ r = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pow_two x₀, hr, pow_orderOf_eq_one]
  have hmk : ((x₀ ^ r : Q) : Q ⧸ N) = (x₀ : Q ⧸ N) := by
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, pow_two, hy2, one_pow, one_mul]
  have hxZ : x₀ ^ r ∉ center Q := by
    intro h
    apply hyZ
    rw [← hmk, mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp h g]
  refine ⟨x₀ ^ r, orderOf_eq_prime (by rw [pow_two]; exact hx2) fun h => hxZ ?_, hxZ⟩
  rw [h]
  exact one_mem _

end CFSG.ComponentClassification.Sol76T13.Hq4
