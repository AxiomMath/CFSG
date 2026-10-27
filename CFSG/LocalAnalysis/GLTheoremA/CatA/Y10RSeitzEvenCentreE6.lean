module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem seitzEvenCentre_twE6 {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.twE6, 0, 1⟩) : NoncentralWitness K 3 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkfield, hkfin, σ, ⟨e⟩, hS, hL⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_twDerived_data_one K ⟨.twE6, 0, 1⟩ hK rfl rfl
  letI : Field k := hkfield
  letI : Finite k := hkfin
  let Z : Subgroup K := Subgroup.center K
  let P : Sylow 2 Z := default
  let N : Subgroup K := (P : Subgroup Z).map Z.subtype
  have hNZ : N ≤ Z := Subgroup.map_subtype_le _
  have hNnormal : N.Normal := CFSG.GroupTheory.normal_of_le_center hNZ
  haveI : N.Normal := hNnormal
  have hNP2 : IsPGroup 2 N := P.isPGroup'.map Z.subtype
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hNP2
    rw [hm]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hZ12 : Nat.card (Subgroup.center K) ∣ 12 :=
    CFSG.LocalAnalysis.GLTheoremA.center_card_dvd_twelve ⟨.twE6, 0, 1⟩ hK rfl rfl
  have hodd := CFSG.LocalAnalysis.GLTheoremA.odd_card_map_center_quotient_sylow K P N rfl
  have hloc : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ N) :=
    CFSG.LocalAnalysis.GLTheoremA.four_le_localRank_three_of_twoPart_center K hZ12 e hS hL
      N hNZ hodd
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three
      (k := 4) (by norm_num) hloc
  have hUZ : ¬ U ≤ (Subgroup.center K).map (QuotientGroup.mk' N) := by
    intro hUle
    have hdvd : Nat.card U ∣ Nat.card ((Subgroup.center K).map (QuotientGroup.mk' N)) :=
      Subgroup.card_dvd_of_le hUle
    have hUodd : Odd (Nat.card U) := Odd.of_dvd_nat hodd hdvd
    obtain ⟨m, hm⟩ := hU2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hU0 (Subgroup.card_eq_one.1 (by simpa using hm))
    have hUeven : Even (Nat.card U) := by
      rw [hm]
      exact even_iff_two_dvd.2 (dvd_pow_self 2 hm0)
    exact Nat.not_even_iff_odd.mpr hUodd hUeven
  have hqk : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN3
  have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact hNZ
  exact noncentralWitness_three Nat.prime_three (by norm_num)
    (noncentralWitness_of_cover (QuotientGroup.mk'_surjective N) hker Nat.prime_three hqk
      hU2 hUZ ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hEel)
      hEcard hEN)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
