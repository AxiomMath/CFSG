module

import CFSG.Quasithin.EmptyFaithful.S1421QA13aCount
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8TrBaseAux1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G H : Type} [Group G] [Group H] {K : Subgroup G}

theorem ffOutFFE8TrStab_ne_one [Finite G] {E : Subgroup G} {z ν : G} (hE : IsElemAb2 E 3)
    (hν3 : orderOf ν = 3) (hνN : ν ∈ normalizer (E : Set G))
    (hfix : ∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = z) : z ≠ 1 := by
  have hcard : Nat.card E = 8 := by rw [hE.2]; norm_num
  have hν : ν ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ν
    rwa [hν3] at h
  obtain ⟨x, hxE, hx1, hxν⟩ := CFSG.Quasithin.QA13a.exists_fixed_of_order_three hcard hνN hν
  have hcomm : ν * x = x * ν := by
    rw [mul_inv_eq_iff_eq_mul] at hxν
    exact hxν
  rcases hfix x hxE hcomm with h | h
  · exact absurd h hx1
  · intro hz
    exact hx1 (h.trans hz)

theorem ffOutFFE8TrStab_not_le_normalizer {ρ : ↥K →* H} (hρ : Function.Injective ρ)
    {P E : Subgroup G} (hPK : P ≤ K) (hEK : E ≤ K) (h : ¬ P ≤ normalizer (E : Set G)) :
    ¬ ffImg ρ P ≤ normalizer (ffImg ρ E : Set H) := by
  intro hle
  apply h
  intro p hp
  exact ffOutFFE8TrImg_mem_normalizer hρ hEK ⟨p, hPK hp⟩
    (hle (mem_ffImg_iff.mpr ⟨⟨p, hPK hp⟩, hp, rfl⟩))

theorem ffOutFFE8TrMap_le_normalizer {N : Subgroup G} (θ : ↥N →* H) {Y S : Subgroup G}
    (hYS : Y ≤ normalizer (S : Set G)) :
    (Y.subgroupOf N).map θ ≤ normalizer (((S.subgroupOf N).map θ : Subgroup H) : Set H) := by
  rintro _ ⟨y, hy, rfl⟩
  exact ffOutFFE8TrMap_mem_normalizer θ y.2 (hYS (Subgroup.mem_subgroupOf.mp hy))

theorem ffOutFFE8TrStab_range_comp {N Y : Subgroup G} (θ : ↥N →* H) (hYN : Y ≤ N) :
    (θ.comp (Subgroup.inclusion hYN)).range = (Y.subgroupOf N).map θ := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion hYN y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

theorem ffOutFFE8TrStab_pull_back {Y : Subgroup G} {ψ : ↥Y →* H} (hψ : Function.Injective ψ)
    {B' : Subgroup H} (hB' : IsNormalE16In ψ.range B') {y' : H} (hy' : y' ∈ ψ.range)
    (hyB : y' ∉ B') (hc : ∀ b ∈ B', y' * b = b * y') :
    ∃ B : Subgroup G, IsNormalE16In Y B ∧ ∃ y ∈ Y, y ∉ B ∧ ∀ b ∈ B, y * b = b * y := by
  refine ⟨ffOutFFE8TrPull ψ B', ?_, ?_⟩
  · have h := ffOutFFE8TrPull_normalE16 hψ le_rfl hB'
    rwa [ffOutFFE8TrPull_range] at h
  · obtain ⟨y1, rfl⟩ := hy'
    refine ⟨(y1 : G), y1.2, fun hy => hyB ((ffOutFFE8TrPull_coe_mem_iff y1).mp hy), ?_⟩
    intro b hb
    obtain ⟨hbY, hbB⟩ := ffOutFFE8TrPull_mem_iff.mp hb
    have h1 : ψ (y1 * ⟨b, hbY⟩) = ψ (⟨b, hbY⟩ * y1) := by
      rw [map_mul, map_mul]
      exact hc _ hbB
    exact congrArg Subtype.val (hψ h1)

end CFSG.OddStandard.SmallF3.Omega
