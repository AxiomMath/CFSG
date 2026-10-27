module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutExcBurnside
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.TriD4
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.OutStructure CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.TauCetiBridge CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.PlaneCases
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Certificates

theorem kd264Y1OutExc_holds : KD264Y1OutExc := by
  intro d hfin hP _ _ _ _ a ha ha3
  obtain ⟨e, hv⟩ := d
  have hPN : OutPNice 3 (TauCeti.CFSGIndex.lie ⟨e, hv⟩).Group := by
    rcases hP with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl |
      ⟨q, rfl⟩
    ·
      have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group .E7 q.p
          q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.e7 (MulEquiv.refl _)⟩
      exact outPNice_E7_gen Nat.prime_three (by norm_num) hm
    ·
      have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group .E8 q.p
          q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.e8 (MulEquiv.refl _)⟩
      exact outPNice_E8_gen Nat.prime_three hm
    ·
      have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group .F4 q.p
          q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.f4 (MulEquiv.refl _)⟩
      by_cases h2 : q.p = 2
      · rw [h2] at hm
        exact outPNice_F4 Nat.prime_three hm
      · exact outPNice_F4_odd Nat.prime_three h2 hm
    ·
      have hq3 : 3 ≤ q.p ^ q.exponent := by
        rw [← TauCeti.PrimePower.card_def]
        exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
          ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
      have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p
          q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩,
          untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.g2 (MulEquiv.refl _)⟩
      by_cases h2 : q.p = 2
      · rw [h2] at hm
        exact outPNice_G2 Nat.prime_three hm
      · by_cases h3 : q.p = 3
        · rw [h3] at hm
          exact outPNice_G2_three Nat.prime_three hm
        · exact outPNice_G2_odd Nat.prime_three h2 h3 hm
    ·
      have hmodel : ReeTitsModel (Cat ⟨.reeF4 k, hv⟩) .twistedF4 2 (2 * k + 1) :=
        reeTitsModel_cat_reeF4 hv
      exact outPNice_twistedF4 Nat.prime_three hmodel
    ·
      have hmodel : ReeTitsModel (Cat ⟨.reeG2 k, hv⟩) .twistedG2 3 (2 * k + 1) :=
        reeTitsModel_reeG2 k ⟨hv, ⟨MulEquiv.refl _⟩⟩
      exact CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 Nat.prime_three hmodel
    ·
      have hmodel : SuzukiModel (Cat ⟨.suzuki k, hv⟩) 2 (2 * k + 1) := suzukiModel_cat hv
      exact outPNice_Suzuki Nat.prime_three hmodel
    ·
      have hT := card_cat_tits_outer hv
      have hout : ¬ 3 ∣ Nat.card (Outer (Cat ⟨.tits, hv⟩)) := by
        rw [hT.2]
        norm_num
      exact outPNice_of_not_dvd_outer Nat.prime_three hout
    ·
      obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eB⟩⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
      letI := hfield
      letI := hfinite
      haveI : Finite (ModGL Tag.D4 K) := finite_modGL
      haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
      have hCE : ChevalleyExceptionalModel ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
          .trialityD4 q.p q.exponent :=
        CFSG.HardMathSupport.Dickson.Sec6.chevalleyExceptionalModel_trialityD4_of_equiv
          q.prime_p q.exponent_pos hK σ hσ (MulEquiv.refl _)
      have hPN : OutPNice 3 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
        by_cases h2 : q.p = 2
        · rw [h2] at hCE
          exact outPNice_trialityD4 Nat.prime_three hCE
        · exact outPNice_trialityD4_odd Nat.prime_three h2 hCE
      exact OutPNice.of_mulEquiv eB hPN
  exact mem_inner_of_mem_innAutDerived_of_outPNice_three hPN ha ha3

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
