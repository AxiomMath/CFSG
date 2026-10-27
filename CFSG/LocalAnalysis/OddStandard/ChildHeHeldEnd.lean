module

public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section HeldEnd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem one_le_open_pRank_centralizer_of_standard (hL : standardComponentIsStandard L) :
    1 ≤ Open.pRank 2 (centralizer (L : Set G)) := by
  obtain ⟨t, htC, ht⟩ := exists_involution_of_standard hL
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp ht).1
  refine SectionRank.le_pRank (by decide) (Subgroup.zpowers_le.mpr htC)
    ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩ (by rw [Nat.card_zpowers, ht, pow_one])
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self t i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem pRank_centralizer_eq_one_of_standard (hL : standardComponentIsStandard L)
    (h : ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G))) :
    CFSG.pRank 2 (centralizer (L : Set G)) = 1 := by
  have h1 := one_le_open_pRank_centralizer_of_standard hL
  have e : CFSG.pRank 2 (centralizer (L : Set G)) = Open.pRank 2 (centralizer (L : Set G)) :=
    (SectionRank.pRank_eq_open_pRank_top 2 _).trans
      (SectionRank.pRank_eq_pRank_top_subgroup (p := 2) (centralizer (L : Set G))).symm
  omega

theorem nonempty_mulEquiv_he_of_center_eq_bot {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    (hHe : IsSporadic (L ⧸ Subgroup.center L) .He) : Nonempty (L ≃* NativeSporadic.He) := by
  obtain ⟨e⟩ : Nonempty ((L ⧸ Subgroup.center L) ≃* NativeSporadic.He) := hHe
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

end HeldEnd

end CFSG.OddStandard
