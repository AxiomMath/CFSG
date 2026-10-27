module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PReeDiagCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158FgExc
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporMathieu
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.Holt.PointHullTwoGroupBasic
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LieType.Ree.ReeGenericPerfect
import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
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
public import Certificates.Certificate2012
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate5133
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate18000
public import Certificates.Certificate1952
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Holds
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
import CFSG.RankThree.PartOne.CTP.StdSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LieType.Ree
open CFSG.LocalAnalysis.GLTheoremA (InnerOn)

open CFSG.LocalAnalysis.GLTheoremA.S10 (InnDiagOn)



private theorem exists_reeF4_of_isReeF4Idx {d : TauCeti.LieTypeIndex} (h : isReeF4Idx d) :
    ∃ m, d = .reeF4 m := by
  cases d with
  | reeF4 m => exact ⟨m, rfl⟩
  | A r q => exact absurd h (by simp [isReeF4Idx])
  | twistedA r q => exact absurd h (by simp [isReeF4Idx])
  | B r q => exact absurd h (by simp [isReeF4Idx])
  | C r q => exact absurd h (by simp [isReeF4Idx])
  | D r q => exact absurd h (by simp [isReeF4Idx])
  | twistedD r q => exact absurd h (by simp [isReeF4Idx])
  | E6 q => exact absurd h (by simp [isReeF4Idx])
  | E7 q => exact absurd h (by simp [isReeF4Idx])
  | E8 q => exact absurd h (by simp [isReeF4Idx])
  | F4 q => exact absurd h (by simp [isReeF4Idx])
  | G2 q => exact absurd h (by simp [isReeF4Idx])
  | twistedE6 q => exact absurd h (by simp [isReeF4Idx])
  | trialityD4 q => exact absurd h (by simp [isReeF4Idx])
  | suzuki m => exact absurd h (by simp [isReeF4Idx])
  | reeG2 m => exact absurd h (by simp [isReeF4Idx])
  | tits => exact absurd h (by simp [isReeF4Idx])

theorem exists_reeF4_data {S : Type} [Group S] [Finite S]
    (hcat : catalogIs S (onLie (CharTwoOf isReeF4Idx))) :
    ∃ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid),
      IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) := by
  obtain ⟨d, hv, ⟨hidx, -⟩, ⟨eS⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  obtain ⟨m, rfl⟩ := exists_reeF4_of_isReeF4Idx hidx
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hfield, hfinite, hcharK, hKcard, ⟨eK⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
  letI := hfield
  letI := hfinite
  haveI : CharP K ReeTag.F4.prime := hcharK
  let e : S ≃* ↥(ReeTag.F4.reeGamma K m) := eS.trans eK
  haveI : IsSimpleGroup ↥(ReeTag.F4.reeGamma K m) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hm1 hKcard
  have hΓ : ∃ a b : ↥(ReeTag.F4.reeGamma K m), a * b ≠ b * a :=
    CFSG.LieType.Ree.LargeReeInvolution.exists_mul_ne_mul_of_commutator_eq_top
      (ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hm1 hKcard)
  refine ⟨m, hv, e.isSimpleGroup, ?_, ⟨eS⟩⟩
  obtain ⟨a, b, hab⟩ := hΓ
  exact ⟨e.symm a, e.symm b, fun h =>
    hab (by simpa using congrArg e h)⟩

theorem reeF4Diag_holds : SimpleDiagModel (CharTwoOf isReeF4Idx) := by
  intro S _ _ p hp hp2 hcat hshape
  intro x y hx1 hxp hyp hcomm J hJ hyN
  obtain ⟨m, hv, hS, hnc, ⟨eS⟩⟩ := exists_reeF4_data hcat
  haveI : IsSimpleGroup S := hS
  haveI : Fact p.Prime := ⟨hp⟩
  have hm : orderOf x = p := orderOf_eq_prime hxp hx1
  have hyc : y ∈ Subgroup.centralizer ({x} : Set S) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hSqS : CFSG.Open.IsQuasisimple S :=
    CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hnc
  have hdvd : p ∣ Nat.card S := hm ▸ orderOf_dvd_natCard x
  have hchevS : IsChevSimple 2 S := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    rcases i with _ | _ | idx | _
    · exact absurd hi id
    · exact absurd hi id
    · exact Or.inl ⟨.lie idx, by simpa [onLie] using hi.2, ⟨e⟩⟩
    · exact absurd hi id
  have hInner : InnerOn J y := by
    have h3le : 3 ≤ p := by have := hp.two_le; omega
    rcases eq_or_lt_of_le h3le with h3 | h3
    · have hp3 : p = 3 := h3.symm
      rw [hp3] at hJ hm
      exact inner_of_glaPComponent_reeF4_three m hv hnc eS x hm hJ y hyc
    · exact inner_of_glaPComponent_reeF4_of_three_lt m hv hnc eS hp h3 x hm hJ y hyc
  have hchev : IsChevSimple 2 (PSimple p J) := by
    have hSqTop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup S) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hSqS
    have hSpTop : GLAPPrimeCore p ↥(⊤ : Subgroup S) = ⊥ := by
      haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
      refine CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup
        hp ?_
      rw [Subgroup.card_top]
      exact hdvd
    have hScTop : IsChevSimple 2 (PSimple p (⊤ : Subgroup S)) := by
      have hIself : GLAPComponent p (⊤ : Subgroup S) (⊤ : Subgroup S) :=
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.glaPComponent_self_of_dvd_card hp hSqTop
          (by rw [Subgroup.card_top]; exact hdvd)
      obtain ⟨eTop⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.KDSpor.nonempty_pSimple_top_equiv hp hnc hIself
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr eTop.symm hchevS
    have hxN : x ∈ Subgroup.normalizer ((⊤ : Subgroup S) : Set S) :=
      Subgroup.mem_normalizer_iff.mpr fun _ => Iff.rfl
    have hcompTop : GLAPComponent p ((⊤ : Subgroup S) ⊓
        Subgroup.centralizer ({x} : Set S)) J := by
      rwa [top_inf_eq]
    exact CFSG.LocalAnalysis.GLTheoremA.T158.isChevSimple_comp_of_kd
      (Ω := S) (S := (⊤ : Subgroup S)) (x := x) (J := J)
      hp (CFSG.LocalAnalysis.GLTheoremA.T158.kdChevDownQ_two_holds hp hp2)
      hSqTop hSpTop hScTop hxN hxp hcompTop
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innDiagOn_of_innerOn hp hJ hchev hyN hInner

end CFSG.LocalAnalysis.GLTheoremA.F151

end
