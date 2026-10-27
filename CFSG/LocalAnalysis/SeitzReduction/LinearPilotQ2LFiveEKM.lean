module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESwap
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

@[expose] def LFourFourCentralizerOrderThreeInput : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 4 2 2 → ∀ x : X, orderOf x = 3 →
    ∃ P : Subgroup X, P ≤ centralizer ({x} : Set X) ∧ ⁅P, P⁆ = P ∧ 5 ∣ Nat.card P

theorem lFiveFieldNOneLiftInput_of_model (hmod : LFourFourCentralizerOrderThreeInput) :
    LFiveFieldNOneLiftInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Ks hKs hKsm hLKs a b hab
    hca hcb X₀ hX₀ hX₀c
  set N₁ := normalizer (W₁ : Set G) with hN₁
  set W' : Subgroup N₁ := W₁.subgroupOf N₁ with hW'
  set π := QuotientGroup.mk' W' with hπ
  set X := modelToG e X₀ with hXdef
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  have hab' : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_compl, Finset.mem_singleton]
    rcases hy with rfl | rfl
    · exact fun h => hca h.symm
    · exact fun h => hcb h.symm
  have hXL₁ : X ≤ L₁ := modelToG_mono e (hX₀.trans (blockSL_mono hab'))
  have hXN : X ≤ N₁ := hXL₁.trans hLN
  have hXc : Nat.card X = 3 := by
    rw [hXdef, modelToG, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hX₀c, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXc])
  have hxo' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hxo]
  set x' : N₁ := ⟨x, hXN x.2⟩ with hx'
  have hx'o : orderOf x' = 3 := by
    rw [← Subgroup.orderOf_coe, hx']
    exact hxo'
  have hW'c : Nat.card W' = 2 ^ 8 := by
    rw [hW', ← hW₁c]
    exact Nat.card_congr (subgroupOfEquivOfLe (le_normalizer)).toEquiv
  have hxbar : orderOf (π x') = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hx'o, pow_orderOf_eq_one, map_one]
    · intro h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have hdvd : orderOf x' ∣ Nat.card W' := by
        have := orderOf_dvd_natCard (⟨x', h1⟩ : W')
        rwa [Subgroup.orderOf_mk] at this
      rw [hx'o, hW'c] at hdvd
      norm_num at hdvd
  have hxK : π x' ∈ Ks := hLKs ⟨x', mem_subgroupOf.2 (hXL₁ x.2), rfl⟩
  have hxKo : orderOf (⟨π x', hxK⟩ : Ks) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxbar
  obtain ⟨Pb, hPbC, hPbperf, hPb5⟩ := hmod Ks hKsm ⟨π x', hxK⟩ hxKo
  set Pb' : Subgroup (seitzBar W₁) := Pb.map Ks.subtype with hPb'
  have hPb'perf : ⁅Pb', Pb'⁆ = Pb' := by rw [hPb', ← map_commutator, hPbperf]
  have hPb'5 : 5 ∣ Nat.card Pb' := by
    rw [hPb', Subgroup.card_map_of_injective Ks.subtype_injective]
    exact hPb5
  set X' : Subgroup N₁ := X.subgroupOf N₁ with hX'
  have hX'c : Nat.card X' = 3 := by
    rw [hX', ← hXc]
    exact Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv
  have hX'p : IsPGroup 3 X' := IsPGroup.of_card (n := 1) (by rw [hX'c, pow_one])
  have hzp : ∀ y ∈ X', ∃ k : ℤ, y = x' ^ k := by
    intro y hy
    have hy' : (⟨(y : G), mem_subgroupOf.1 hy⟩ : X) ∈ zpowers x := by
      have hz : zpowers x = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hxo, hXc]
      rw [hz]
      exact mem_top _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy'
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow] at this
    rw [Subgroup.coe_zpow]
    exact this.symm
  have hPbX : Pb' ≤ centralizer ((X'.map π : Subgroup (seitzBar W₁)) : Set (seitzBar W₁)) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := hzp y hy
    have hpx : (⟨π x', hxK⟩ : Ks) * p = p * ⟨π x', hxK⟩ :=
      (mem_centralizer_singleton_iff.1 (hPbC hp)).symm
    have hpx' : π x' * (p : seitzBar W₁) = p * π x' := congrArg Subtype.val hpx
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (π x') (p : seitzBar W₁) from hpx') k).eq
  have hcop : ¬ 3 ∣ Nat.card W' := by
    rw [hW'c]
    norm_num
  have hmapC := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 W' hcop X' hX'p
  set Q : Subgroup N₁ := centralizer (X' : Set N₁) ⊓ Pb'.comap π with hQ
  have hQmap : Q.map π = Pb' := by
    refine le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _)) fun y hy => ?_
    have hy' : y ∈ (centralizer (X' : Set N₁)).map π := by
      rw [hmapC]
      exact hPbX hy
    obtain ⟨z, hz, rfl⟩ := hy'
    exact ⟨z, mem_inf.2 ⟨hz, hy⟩, rfl⟩
  have hP₀map : (perfectCore Q).map π = Pb' := by
    rw [CFSG.Quasithin.map_perfectCore, hQmap,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hPb'perf]
  refine ⟨(perfectCore Q).map N₁.subtype, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨p, hp, rfl⟩
    have hpQ : p ∈ centralizer (X' : Set N₁) :=
      (mem_inf.1 (CFSG.Quasithin.perfectCore_le Q hp)).1
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := mem_centralizer_iff.1 hpQ ⟨y, hXN hy⟩ (mem_subgroupOf.2 hy)
    exact congrArg Subtype.val h1
  · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
  · rw [Subgroup.card_map_of_injective N₁.subtype_injective]
    exact hPb'5.trans (hP₀map ▸ Subgroup.card_map_dvd (perfectCore Q) π)

end CFSG.SeitzReduction.LinearPilot
