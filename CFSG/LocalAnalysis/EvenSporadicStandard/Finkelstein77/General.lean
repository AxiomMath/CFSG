module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Main

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.Assembly.ComponentType CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.GH74

theorem odd_inf_of_lemma25 {G : Type} [Group G] [Finite G] (hO : CFSG.Assembly.oddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S) (h4 : 4 ≤ Nat.card S)
    (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L)) (h25 : Asc76Lemma25)
    (hLX : ¬ L.Normal → ∀ y ∈ centralizer (L : Set G), orderOf y = 2 → L ≤ normalClosure {y})
    (hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
        IsPGroup 2 P → Nat.card P ≤ 2) :
    ∀ g : G, g ∉ normalizer (L : Set G) →
      Odd (Nat.card ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
        normalizer (L : Set G) : Subgroup G)) := by
  classical
  intro g hg
  exfalso
  have hnorm : ¬ L.Normal := fun h => hg (by
    rw [Subgroup.normalizer_eq_top_iff.mpr h]
    exact mem_top g)
  obtain ⟨y, hy⟩ := exists_orderOf_four_of_cyclic_sylow S hS h4
  have hyC : (y : G) ∈ centralizer (L : Set G) := y.2
  have hy4 : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy]
  have hW := weaklyClosed_zpowers hL S hS hall hyC hy4
  have hz2 : orderOf ((y : G) ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy4]; norm_num), hy4]
  have hzC : (y : G) ^ 2 ∈ centralizer (L : Set G) := pow_mem hyC 2
  by_cases hZ : InZStar ((y : G) ^ 2)
  · obtain ⟨N', hN', hodd, hcomm⟩ := hZ
    have hN'le : N' ≤ CFSG.Assembly.oddCore G := le_sSup ⟨hN', hodd⟩
    rw [hO, le_bot_iff] at hN'le
    have hcen : (y : G) ^ 2 * g = g * (y : G) ^ 2 := by
      have h := hcomm g
      rw [hN'le, mem_bot, mul_inv_eq_one] at h
      calc (y : G) ^ 2 * g = (g * (y : G) ^ 2 * g⁻¹) * g := by rw [h]
        _ = g * (y : G) ^ 2 := by group
    exact hg ((CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hL hzC hz2).1 (mem_centralizer_singleton_iff.mpr hcen.symm))
  · have h2 := sectionalTwoRankLE_normalClosure_of_lemma25 h25 hy4 hW hZ
    have hLX' := hLX hnorm _ hzC hz2
    have hL2 : SectionalTwoRankLE L 2 :=
      SectionalTwoRankLE.of_mulEquiv (subgroupOfEquivOfLe hLX') (h2.subgroup _)
    have hbound := (hL2.quotient (center L)).twoRank_le
    omega

theorem normal_of_four_le_card_sylow {G : Type} [Group G] [Finite G]
    (hO : CFSG.Assembly.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (hI : HypothesisOne (L ⧸ center L)) (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L))
    (h25 : Asc76Lemma25)
    (hLX : ¬ L.Normal → ∀ y ∈ centralizer (L : Set G), orderOf y = 2 → L ≤ normalClosure {y})
    (h4 : 4 ≤ Nat.card S) : L.Normal :=
  standard_cyclic_centralizer_normal hL hO S hS hI
    (fun hall => odd_inf_of_lemma25 hO hL S hS h4 hrank h25 hLX hall) h4

theorem card_sylow_eq_two_of_not_normal_of_lemma25 {G : Type} [Group G] [Finite G]
    (hO : CFSG.Assembly.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (hI : HypothesisOne (L ⧸ center L)) (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L))
    (h25 : Asc76Lemma25)
    (hLX : ¬ L.Normal → ∀ y ∈ centralizer (L : Set G), orderOf y = 2 → L ≤ normalClosure {y})
    (hnot : ¬ L.Normal) : Nat.card S = 2 := by
  by_contra hne
  exact hnot (normal_of_four_le_card_sylow hO hL S hS hI hrank h25 hLX
    (four_le_card_sylow_of_ne_two S hL.2.1 hne))

end CFSG.EvenSporadicStandard.Finkelstein77
