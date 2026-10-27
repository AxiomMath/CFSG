module

public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Walter.AStar.Subnormal
import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.Open.QuasithinDefs
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Core

variable {Y : Type*} [Group Y] [Finite Y]

theorem odd_card_of_card_le_two_of_sup_zpowers {C : Subgroup Y} {s : Y} (hs : orderOf s = 2)
    (hsN : s ∈ normalizer (C : Set Y)) (hsC : s ∉ C)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ C ⊔ zpowers s → Nat.card U ≤ 2) :
    Odd (Nat.card C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (C ⊔ zpowers s : Subgroup Y) = Nat.card C * 2 := by
    rw [← hs]
    refine CFSG.LieType.Steinberg.card_sup_zpowers hsN fun k hk => ?_
    have h2 : ((orderOf s : ℕ) : ℤ) = 2 := by rw [hs]; norm_num
    rw [← zpow_mod_orderOf, h2] at hk ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hk
      exact absurd hk hsC
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨c, hc⟩ := hodd
  have h4 : 2 ^ 2 ∣ Nat.card (C ⊔ zpowers s : Subgroup Y) := ⟨c, by rw [hcard, hc]; ring⟩
  obtain ⟨U, hU⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  have hUc : Nat.card (U.map (C ⊔ zpowers s).subtype) = 2 ^ 2 := by
    rw [card_map_of_injective (subtype_injective _), hU]
  have hle := hsyl _ (IsPGroup.of_card hUc) (map_subtype_le U)
  rw [hUc] at hle
  norm_num at hle

omit [Finite Y] in
theorem mul_mul_inv_mem_centralizer_of_mem_normalizer {Kc : Subgroup Y} {s a : Y}
    (hs : s ∈ normalizer (Kc : Set Y)) (ha : a ∈ centralizer (Kc : Set Y)) :
    s * a * s⁻¹ ∈ centralizer (Kc : Set Y) := by
  rw [mem_centralizer_iff] at ha ⊢
  intro k hk
  have hk' : s⁻¹ * k * s⁻¹⁻¹ ∈ Kc := (mem_normalizer_iff.mp (inv_mem hs) k).mp hk
  rw [inv_inv] at hk'
  have h := ha _ hk'
  calc k * (s * a * s⁻¹) = s * ((s⁻¹ * k * s) * a) * s⁻¹ := by group
    _ = s * (a * (s⁻¹ * k * s)) * s⁻¹ := by rw [h]
    _ = s * a * s⁻¹ * k := by group

theorem odd_card_centralizer_of_le {Kc D : Subgroup Y} (hDK : D ≤ Kc) {s : Y}
    (hs : orderOf s = 2) (hsD : s ∈ centralizer (D : Set Y)) (hsN : s ∈ normalizer (Kc : Set Y))
    (hsC : s ∉ centralizer (Kc : Set Y))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    Odd (Nat.card (centralizer (Kc : Set Y))) := by
  have hsNC : s ∈ normalizer (centralizer (Kc : Set Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro a
    refine ⟨fun ha => mul_mul_inv_mem_centralizer_of_mem_normalizer hsN ha, fun ha => ?_⟩
    have h := mul_mul_inv_mem_centralizer_of_mem_normalizer (inv_mem hsN) ha
    rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
      mul_one] at h
  have hCD : centralizer (Kc : Set Y) ⊔ zpowers s ≤ centralizer (D : Set Y) :=
    sup_le (centralizer_le hDK) ((zpowers_le (G := Y)).mpr hsD)
  exact odd_card_of_card_le_two_of_sup_zpowers hs hsNC hsC
    fun U hU hUle => hsyl U hU (hUle.trans hCD)

theorem eq_of_isComponent_of_odd_card_centralizer (hO : pPrimeCore 2 Y = ⊥)
    {Kc J : Subgroup Y} (hKc : IsComponent Kc)
    (hodd : Odd (Nat.card (centralizer (Kc : Set Y)))) (hJ : IsComponent J) : J = Kc := by
  rcases CFSG.LocalCores.distinct_components_commute hJ hKc with h | h
  · exact h
  · exfalso
    have hJC : J ≤ centralizer (Kc : Set Y) := commutator_eq_bot_iff_le_centralizer.mp h
    have hbot := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hJ.2
      (Odd.of_dvd_nat hodd (card_dvd_of_le hJC))
    have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this hbot

theorem centralizer_eq_bot_and_normal_of_isComponent (hO : pPrimeCore 2 Y = ⊥)
    {Kc D : Subgroup Y} (hKc : IsComponent Kc) (hDK : D ≤ Kc) {s : Y} (hs : orderOf s = 2)
    (hsD : s ∈ centralizer (D : Set Y)) (hsN : s ∈ normalizer (Kc : Set Y))
    (hsC : s ∉ centralizer (Kc : Set Y))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2) :
    centralizer (Kc : Set Y) = ⊥ ∧ Kc.Normal := by
  have hCodd := odd_card_centralizer_of_le hDK hs hsD hsN hsC hsyl
  have hnorm : Kc.Normal := ⟨fun k hk y => by
    rw [← eq_of_isComponent_of_odd_card_centralizer hO hKc hCodd
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hKc)]
    exact ⟨k, hk, rfl⟩⟩
  have hCn : (centralizer (Kc : Set Y)).Normal := Subgroup.normal_centralizer
  exact ⟨CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hCn.isSubnormal hCodd, hnorm⟩

theorem perfectCore_top_eq_of_isComponent (hO : pPrimeCore 2 Y = ⊥)
    {Kc D : Subgroup Y} (hKc : IsComponent Kc) (hDK : D ≤ Kc) {s : Y} (hs : orderOf s = 2)
    (hsD : s ∈ centralizer (D : Set Y)) (hsN : s ∈ normalizer (Kc : Set Y))
    (hsC : s ∉ centralizer (Kc : Set Y))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hOut : Group.IsSolvable (Outer Kc)) :
    perfectCore (⊤ : Subgroup Y) = Kc := by
  obtain ⟨hCbot, hnorm⟩ :=
    centralizer_eq_bot_and_normal_of_isComponent hO hKc hDK hs hsD hsN hsC hsyl
  have hKperf : ⁅Kc, Kc⁆ = Kc := isPerfect_iff.mp hKc.1.1
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKperf)
  have hK : Group.IsSolvable (centralizer (Kc : Set Y) ⊓ ⊤ : Subgroup Y) := by
    rw [inf_top_eq, hCbot]
    infer_instance
  refine CFSG.SeitzReduction.perfect_le_of_isSolvable_outer hOut le_top ?_ hK
    (CFSG.Quasithin.perfectCore_perfect _) le_top
  rw [normalizer_eq_top_iff.mpr hnorm]

end Core

end CFSG.SeitzReduction.LinearPilot
