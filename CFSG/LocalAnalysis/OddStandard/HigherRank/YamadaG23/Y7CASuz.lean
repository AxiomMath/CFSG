module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Rank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem y7c_two_group_cent_two {W : Type} [Group W] [Finite W] (hW : IsPGroup 2 W) {t : W}
    (ht1 : t ≠ 1) (hc : Nat.card ↥(centralizer ({t} : Set W)) ≤ 2) : Nat.card W ≤ 2 := by
  classical
  haveI : Nontrivial W := ⟨⟨t, 1, ht1⟩⟩
  haveI : Nontrivial ↥(center W) := hW.center_nontrivial
  have hZle : center W ≤ centralizer ({t} : Set W) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_center_iff.mp hx y
  have hZcard : 2 ≤ Nat.card ↥(center W) := Finite.one_lt_card
  have hCcard : Nat.card ↥(centralizer ({t} : Set W)) = Nat.card ↥(center W) :=
    le_antisymm (hc.trans hZcard) (Subgroup.card_le_of_le hZle)
  have hCeq : center W = centralizer ({t} : Set W) :=
    Subgroup.eq_of_le_of_card_ge hZle hCcard.le
  have htZ : t ∈ center W := by
    rw [hCeq]
    exact mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy])
  have hall : centralizer ({t} : Set W) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_center_iff.mp htZ y).symm
  rw [← Subgroup.card_top, ← hall]
  exact hc

theorem y7c_suzuki_le_four {W : Type} [Group W] [Finite W] (hW : IsPGroup 2 W) {t : W}
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hc : Nat.card ↥(centralizer ({t} : Set W)) ≤ 4)
    {E : Subgroup W} (hE : ∀ y ∈ E, y * y = 1) : Nat.card E ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht ht1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (hW.to_subgroup (centralizer ({t} : Set W)))
  have htC : t ∈ centralizer ({t} : Set W) := mem_centralizer_iff.mpr (fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy])
  have hCnt : 1 < Nat.card ↥(centralizer ({t} : Set W)) := by
    haveI : Nontrivial ↥(centralizer ({t} : Set W)) := ⟨⟨⟨t, htC⟩, 1, fun h => ht1 (by
      simpa using congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      omega
    · exact h0
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h8 : 2 ^ 3 ≤ Nat.card ↥(centralizer ({t} : Set W)) := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8
    omega
  have hEW : Nat.card E ≤ Nat.card W := Subgroup.card_le_card_group E
  have hcases : Nat.card ↥(centralizer ({t} : Set W)) = 2 ∨
      Nat.card ↥(centralizer ({t} : Set W)) = 4 := by
    interval_cases k
    · left
      simpa using hk
    · right
      simpa using hk
  rcases hcases with h2 | h4
  · have := y7c_two_group_cent_two hW ht1 h2.le
    omega
  · exact CFSG.ComponentClassification.Sol76T13.R12.card_le_four_of_card_centralizer hW hord h4 hE

end CFSG.OddStandard.HigherRank.YamadaG23
