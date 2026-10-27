module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Comp
public import CFSG.Blueprint.Chevalley
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoPlumb
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcE678
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup b3Lie_fixSubgroup_conj)

theorem componentsNoD4_adjointGroup
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {α : MulAut ↥(adjointGroup τ K)} (hα3 : α ^ 3 = 1) :
    ComponentsNoD4 α := by
  intro I hI
  obtain ⟨s, hs⟩ : ∃ s, α = MulAut.conj s := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_eq_conj_of_pow_three_F4 hK hα3
    · exact CFSG.LocalAnalysis.GLTheoremA.T171S.exists_eq_conj_of_pow_three_E6 hK hα3
    · exact CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_card_eq_two (Or.inl rfl) hK α
    · exact CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_card_eq_two (Or.inr rfl) hK α
  have hrat : CFSG.StandardType.ExcThreeTwoRatNotExc τ := by
    rcases hτ with rfl | rfl | rfl | rfl
    exacts [CFSG.StandardType.excThreeTwoRatNotExc_F4, CFSG.StandardType.excThreeTwoRatNotExc_E6,
      CFSG.StandardType.excThreeTwoRatNotExc_E7, CFSG.StandardType.excThreeTwoRatNotExc_E8]
  have hcomp := CFSG.StandardType.ExcThreeAtTwo.centCompNotExcThreeAt_three_adjointGroup hτ hrat hK
  have hs3 : s ^ 3 = 1 := by
    have hconj : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, ← hs, hα3]
    have hmem := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
  rw [hs, b3Lie_fixSubgroup_conj] at hI
  exact (hcomp s hs3 I (CFSG.Assembly.isComponentOf_iff_open.mpr hI)).1

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
