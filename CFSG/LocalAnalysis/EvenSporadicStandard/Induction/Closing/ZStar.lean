module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar
public import CFSG.LocalAnalysis.ZStar
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

theorem odd_normal_eq_bot_of_fStar (hN : FStarSimple N) {P : Subgroup H} (hP : P.Normal)
    (hodd : Odd (Nat.card P)) : P = ⊥ := by
  have hNn : N.Normal := hN.normal
  have := hN.isSimpleGroup
  have hnorm : (P.subgroupOf N).Normal := hP.subgroupOf N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf N) with h | h
  · have hdis : Disjoint P N := by
      rw [← Subgroup.subgroupOf_eq_bot]
      exact h
    have hcomm : P ≤ centralizer (N : Set H) := by
      intro x hx
      refine mem_centralizer_iff.2 fun y hy => ?_
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ N := by
        refine ⟨?_, ?_⟩
        · have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [this]
          exact P.mul_mem hx (hP.conj_mem _ (P.inv_mem hx) y)
        · have : x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ := by group
          rw [this]
          exact N.mul_mem (hNn.conj_mem y hy x) (N.inv_mem hy)
      rw [hdis.eq_bot, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    refine eq_bot_iff.2 fun x hx => ?_
    have hxN : x ∈ N := hN.centralizer_le (hcomm hx)
    have : x ∈ P ⊓ N := ⟨hx, hxN⟩
    rw [hdis.eq_bot] at this
    exact this
  · exfalso
    have hNP : N ≤ P := Subgroup.subgroupOf_eq_top.1 h
    have hoddN : Odd (Nat.card N) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hNP)
    have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddN
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥N)).2 hsolv a b)

theorem exists_fused_commuting_involution_of_fStar (hN : FStarSimple N) {t : H}
    (ht : orderOf t = 2) :
    ∃ g : H, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  classical
  by_contra hcon
  have hiso : ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t :=
    fun g hg => by_contra fun hne => hcon ⟨g, hne, hg⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have := Fintype.ofFinite H
  obtain ⟨P, hP, hodd, hPt⟩ := CFSG.ZStar.glauberman_zStar H t ht1 ht2 hiso
  have hP1 : P = ⊥ := odd_normal_eq_bot_of_fStar hN hP hodd
  have hcent : ∀ g : H, g * t = t * g := by
    intro g
    have h1 := hPt g
    rw [hP1, mem_bot, mul_inv_eq_one] at h1
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]
  have htN : t ∈ N := hN.centralizer_le (mem_centralizer_iff.2 fun y _ => hcent y)
  have hz : (⟨t, htN⟩ : ↥N) ∈ center ↥N := mem_center_iff.2 fun g => Subtype.ext (hcent g)
  have := hN.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥N) with h | h
  · rw [h, mem_bot] at hz
    exact ht1 (congrArg Subtype.val hz)
  · obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

end CFSG.EvenSporadicStandard.Induction.Closing
