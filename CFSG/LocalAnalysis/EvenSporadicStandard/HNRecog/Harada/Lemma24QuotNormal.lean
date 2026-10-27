module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Cfg

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem odd_normal_quot {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    ∀ N : Subgroup (Y ⧸ zpowers a), N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hNnorm hNodd
  let π : Y →* Y ⧸ zpowers a := QuotientGroup.mk' (zpowers a)
  let N' : Subgroup Y := N.comap π
  have hN'norm : N'.Normal := hNnorm.comap π
  have hcard : Nat.card N' = 3 * Nat.card N := by
    have hcard' := Nat.card_congr
      (QuotientGroup.preimageMkEquivSubgroupProdSet (zpowers a) (N : Set (Y ⧸ zpowers a)))
    rw [Nat.card_prod, Nat.card_zpowers, h.orderOf_a] at hcard'
    have hN'set : (N' : Set Y) = QuotientGroup.mk ⁻¹' (N : Set (Y ⧸ zpowers a)) := rfl
    rw [← hN'set] at hcard'
    exact hcard'
  have hN'odd : Odd (Nat.card N') := by
    rw [hcard]
    exact (by norm_num : Odd 3).mul hNodd
  have hle : N' ≤ zpowers a :=
    normal_odd_le_zpowers h.a_central h.orderOf_a h.t_sq h.τ_fusion h.odd_normal h.W_comm
      N' hN'norm hN'odd
  have hmap : N'.map π = N :=
    Subgroup.map_comap_eq_self_of_surjective (f := π)
      (QuotientGroup.mk'_surjective (zpowers a)) N
  have hmapbot : (zpowers a).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    simpa [π] using hx
  apply le_bot_iff.mp
  rw [← hmap]
  exact (Subgroup.map_mono hle).trans (le_of_eq hmapbot)

end CFSG.EvenSporadicStandard.HNRecog.Harada
