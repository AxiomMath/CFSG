module

public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXGF2HigherCenterWidthFour
import CFSG.RankThree.GF2n.QTwo
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open CFSG.Yardstones.M3aba7dc4b8a8 (GF2RankFourSetting coreQ)

abbrev critCenter {G : Type} [Group G] {Q : Subgroup G} (D : Subgroup Q) : Subgroup G :=
  ((center D).map D.subtype).map Q.subtype

structure Setup {G : Type} [Group G] [Finite G] (M B Q : Subgroup G) (z : G)
    (D : Subgroup Q) (k u : ℕ) : Prop where
  charTwoType : IsCharacteristicPType G 2
  oddRank : 4 ≤ CFSG.twoLocalOddRank G
  maxLocal : GLAIsMaxTwoLocal M
  symplectic : GLASymplecticType (pCoreOf 2 M)
  bmax : GLAIsBmax 3 B
  bmax_le : B ≤ M
  core_eq : Q = CFSG.inSubgroup (CFSG.pCore 2) M
  central : z ∈ (center Q).map Q.subtype
  involution : orderOf z = 2
  local_eq : M = centralizer {z}
  critical : ThompsonCritical D
  three_le : 3 ≤ k
  center_card : Nat.card ((center D).map D.subtype) = 2 ^ k
  quotient_card : Nat.card (D ⧸ center D) = 2 ^ (2 * u)
  four_le : 4 ≤ u

theorem exists_setup
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G) (hset : GF2RankFourSetting G z)
    (hnex : ¬ IsExtraspecialPGroup 2 (coreQ z)) (hexp : ∃ x ∈ coreQ z, x ^ 4 ≠ 1) :
    ∃ (B : Subgroup G) (D : Subgroup (coreQ z)) (k u : ℕ),
      Setup (centralizer {z}) B (coreQ z) z D k u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hchar2, he, hz2, hmax, hsymp, B, hB, hBM⟩ := hset
  have hchar : IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hchar2
  have he' : 4 ≤ CFSG.twoLocalOddRank G := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact he
  have hloc : IsPLocal 2 (centralizer ({z} : Set G)) := by
    obtain ⟨P, hP1, hP2, hMP⟩ := hmax.1
    exact ⟨P, hP1, hP2, hMP⟩
  have hF : generalizedFitting ↥(centralizer ({z} : Set G)) =
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :=
    CFSG.RankThree.GF2n.generalizedFitting_eq_pCore hchar hloc
  have hQ : coreQ z = CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({z} : Set G)) := by
    unfold coreQ CFSG.inSubgroup
    rw [hF]
  have hzO : z ∈ pCoreOf 2 (centralizer ({z} : Set G)) := by
    refine hchar2 _ hmax.1 ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    refine mem_centralizer_iff.mpr ?_
    intro x hx
    obtain ⟨x', -, rfl⟩ := hx
    exact mem_centralizer_singleton_iff.mp x'.2
  have hzQ : z ∈ (center (coreQ z)).map (coreQ z).subtype := by
    have hzQ' : z ∈ coreQ z := by
      rw [hQ]
      exact hzO
    refine ⟨⟨z, hzQ'⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    apply Subtype.ext
    have hle : coreQ z ≤ centralizer ({z} : Set G) := by
      rw [hQ]
      exact map_subtype_le _
    exact mem_centralizer_singleton_iff.mp (hle y.2)
  have hQ2 : IsPGroup 2 (coreQ z) := by
    rw [hQ]
    exact IsPGroup.map CFSG.pCore_isPGroup _
  obtain ⟨⟨D, hD⟩, hcc⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_critical_center_and_exponent_four_reduction hchar
      (by omega) hmax hsymp hB hBM hQ hzQ hz2 (r := GLATwoLocalRank 3 G) rfl
  obtain ⟨-, -, hYcyc, -, -, -, -, -, -, -, -, -, -, -, hxor⟩ := hcc D hD _ rfl _ rfl
  have hX := hxor hnex
  have hY8 : 8 ≤ Nat.card ((center D).map D.subtype) := by
    rcases hX with ⟨hA, -⟩ | ⟨⟨h8, -⟩, -⟩
    · obtain ⟨x, hxQ, hx4⟩ := hexp
      exact absurd (hA.1 ⟨x, hxQ⟩) (fun h => hx4 (by simpa using congrArg Subtype.val h))
    · exact h8
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ2.to_subgroup ((center D).map D.subtype))
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hYcard : Nat.card ((center D).map D.subtype) = Nat.card (center D) :=
    Nat.card_congr ((center D).equivMapOfInjective D.subtype D.subtype_injective).symm.toEquiv
  obtain ⟨hEA, u, hu4, hfin, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_higher_center_critical_width_at_least_four_at_rank_four
      hchar he' hmax hsymp hB hBM hQ hD (by omega)
  have hu : Nat.card (D ⧸ center D) = 2 ^ (2 * u) := by
    rw [CFSG.LocalAnalysis.GorensteinLyons.SteinbergBK.natCard_eq_two_pow_finrank, hfin]
  exact ⟨B, D, k, u, ⟨hchar, he', hmax, hsymp, hB, hBM, hQ, hzQ, hz2, rfl, hD, hk3, hk, hu, hu4⟩⟩

end CFSG.GF2Type.Aschbacher1976HigherCenter
