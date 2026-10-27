module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefPSL2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefU3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefSp4
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefG2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3Quot

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix
open scoped MatrixGroups

theorem threeNineDefRankOne_holds : ThreeNineDefRankOne := by
  intro G _ _ p d Y hp hp5 hd hd2 hdp hdG hmodel hY
  have hp2 : p ≠ 2 := by omega
  rcases hmodel with h2 | h3 | h1
  · exact not_isBorelDLocal_psl_two hp hp2 hd hdp hdG h2 hY
  · exact not_isBorelDLocal_psl_two hp hp2 hd hdp hdG h3 hY
  · exact not_isBorelDLocal_psu_three hp hp2 hd hdp hdG h1 hY

theorem threeNineDefL3_holds : ThreeNineDefL3 := by
  intro G _ _ p d Y hp hp5 hd hd2 hdp hdG hK hY
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hK
  have hY₀ : IsBorelDLocal p d (Y.map e.toMonoidHom) := hY.map_equiv e
  have hdG' : d ∣ Nat.card PSL(3, ZMod p) := Nat.card_congr e.toEquiv ▸ hdG
  obtain ⟨hdp1, g, i, hi, hcomap⟩ :=
    exists_conj_comap_eq_flagStabilizer hp5 hd hd2 hdp hdG' hY₀
  have hPSL2₁ : IsPSLType 2 (ZMod p)
      (oPrimeModPrimeComplement d ((Y.map e.toMonoidHom).map
        (MulAut.conj g).toMonoidHom)) :=
    isPSLType_two_oPrimeModPrimeComplement_of_comap_eq_flagStabilizer hp5 hd hd2 hdp1 hi hcomap
  obtain ⟨eY⟩ := oPrimeModPrimeComplement_congr d
    ((Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective).trans
      (Subgroup.equivMapOfInjective (Y.map e.toMonoidHom) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective))
  refine ⟨hdp1, ?_, ?_⟩
  · exact ⟨eY.trans hPSL2₁.some⟩
  · intro S hS _
    have hSmap : IsPGroup d (S.map e.toMonoidHom) := hS.map e.toMonoidHom
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective S e.toMonoidHom e.injective)).mpr
      (isCyclic_of_isPGroup_psl_three hd hd2 hdp1 hSmap)

section G2


theorem threeNineDefOut_holds : ThreeNineDefOut := by
  intro G _ _ p hp hp5 hmember
  have hOutL3 : IsPSLType 3 (ZMod p) G → Nat.card (Outer G) ∣ 2 * Nat.gcd 3 (p - 1) :=
    fun hL3 => (threeNineOut_psl_three hp hp5 hL3).2.2.2.2
  rcases hmember with h2 | h3 | hL3 | hU3 | hSp4 | hG2
  · obtain ⟨hZ, hpout, hout3, h3⟩ := threeNineOut_psl_two hp hp5 (Or.inl rfl) h2
    exact ⟨hZ, hpout, hout3, h3, hOutL3⟩
  · obtain ⟨hZ, hpout, hout3, h3⟩ := threeNineOut_psl_two hp hp5 (Or.inr rfl) h3
    exact ⟨hZ, hpout, hout3, h3, hOutL3⟩
  · obtain ⟨hZ, hpout, hout3, h3, hOut⟩ := threeNineOut_psl_three hp hp5 hL3
    exact ⟨hZ, hpout, hout3, h3, fun _ => hOut⟩
  · obtain ⟨hZ, hpout, hout3, h3⟩ := threeNineOut_psu_three hp hp5 hU3
    exact ⟨hZ, hpout, hout3, h3, hOutL3⟩
  · obtain ⟨hZ, hpout, hout3, h3⟩ := threeNineOut_psp_four hp hp5 hSp4
    exact ⟨hZ, hpout, hout3, h3, hOutL3⟩
  · obtain ⟨hZ, hpout, hout3, h3⟩ := threeNineOut_G2 hp hp5 hG2
    exact ⟨hZ, hpout, hout3, h3, hOutL3⟩

theorem threeNineDefRankTwo_holds : ThreeNineDefRankTwo := by
  intro G _ _ p d Y hp hp5 hd hd2 hdp hdG hmember hY
  rcases hmember with hSp4 | hG2
  · exact not_isBorelDLocal_psp_four hp hp5 hd hd2 hdp hdG hSp4 hY
  · exact not_isBorelDLocal_G2 hp hp5 hd hd2 hdp hdG hG2 hY

theorem threeNineFiveDef_holds : ThreeNineFiveDef :=
  threeNineFiveDef_of_members threeNineDefOut_holds threeNineDefRankOne_holds
    threeNineDefRankTwo_holds threeNineDefL3_holds

end G2

end CFSG.LocalAnalysis.AGL81I.Section3
