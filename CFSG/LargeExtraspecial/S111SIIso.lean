module

public import CFSG.LargeExtraspecial.S111SISigma
public import CFSG.LargeExtraspecial.S111SIGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem not_central_of_mem_Mbar {t : S.O} (htM : t ∈ S.Mbar) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ¬ ∀ x ∈ S.Mbar, x * t * x⁻¹ = t := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)
  have hz : IsPGroup 2 (zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hle : zpowers t ≤ S.Mbar := zpowers_le.mpr htM
  have hN : ((zpowers t).subgroupOf S.Mbar).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    have e : ((x * n * x⁻¹ : S.Mbar) : S.O) = t ^ k := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, ← conj_zpow,
        hc x x.2]
    rw [e]
    exact zpow_mem (mem_zpowers t) k⟩
  have h0 := S5.eq_bot_of_isSubnormal_Mbar S
    (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle hN) hz
  have h1 := mem_zpowers t
  rw [h0, mem_bot] at h1
  exact ht1 h1

theorem isoCfg_of_isolated (hy : Hyp S g) (h6 : 6 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, (x * t * x⁻¹) * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    ∃ y : S.O, IsoCfg S t y := by
  have haQ := hy.hyp4.conj_mem
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have ht2 : t * t = 1 := S4.mul_self_of_mem_Lbar S haQ ht
  have := Fintype.ofFinite S.Mbar
  have ht'1 : (⟨t, htM⟩ : S.Mbar) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'2 : (⟨t, htM⟩ : S.Mbar) * ⟨t, htM⟩ = 1 := Subtype.ext ht2
  obtain ⟨N, hN, hodd, hcomm⟩ := CFSG.ZStar.glauberman_zStar S.Mbar ⟨t, htM⟩ ht'1 ht'2
    fun x hx => Subtype.ext (hiso x x.2 (congrArg Subtype.val hx))
  have hN3 : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le (S5.le_timmesfeldOddCore hN hodd)).trans
    (S5.card_oddCore_dvd_three hy.hyp4 hy.noA2' hy.cons (by omega))
  have hcomm' : ∀ x : S.Mbar, x * ⟨t, htM⟩ * x⁻¹ * (⟨t, htM⟩ : S.Mbar)⁻¹ ∈ N := hcomm
  have hnc : ¬ ∀ x : S.Mbar, x * ⟨t, htM⟩ * x⁻¹ = ⟨t, htM⟩ := fun h =>
    not_central_of_mem_Mbar htM ht2 ht1 fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)
  have hcard : Nat.card N = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hN3 with h | h
    · exfalso
      apply hnc
      intro x
      have h1 := hcomm' x
      rw [Subgroup.card_eq_one.mp h, mem_bot] at h1
      exact mul_inv_eq_one.mp h1
    · exact h
  obtain ⟨y, hS⟩ := exists_inv_of_card_three hN hcard ht'2 hcomm' hnc
  refine ⟨(y : S.O), htM, y.2, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu, hut⟩ := hS.exists_mem_cent ⟨x, hx⟩
    refine ⟨(u : S.O), ?_, congrArg Subtype.val hut⟩
    rcases hu with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rcases hS.commute_or_commute ⟨x, hx⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem false_of_isolated (hy : Hyp S g) (hirr : ¬ S.IsReducible) (h6 : 6 ≤ S.width)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, (x * t * x⁻¹) * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    False := by
  obtain ⟨y, C⟩ := isoCfg_of_isolated hy h6 ht ht1 hiso
  rcases hy.lin ht ht1 with hR | hL
  · exact C.rbar_ne hy hirr h6 ht hR
  · exact C.false_of_linCase hy hirr h6 ht hL

end CFSG.LargeExtraspecial.S11
