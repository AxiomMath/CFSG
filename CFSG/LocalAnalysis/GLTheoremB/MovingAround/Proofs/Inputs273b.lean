module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Spor
public import CFSG.GH74.KGroups.L28
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.PumpDefChar
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs129

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem sporadicLocalOneData_holds :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicLocalOneData :=
  CFSG.HardMathSupport.Timmesfeld.Tables.Census.sporadicLocalOneData_of_pairs_holds
    CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds
    CFSG.HardMathSupport.Timmesfeld.Coordinator.ys03_sporadicLocalOnePairs

theorem sporadicMultipliers_holds :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
  CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

theorem input27_3Spor_of_cube
    (h : Inputs273.SporOneBalanceCube) : Inputs273.Input27_3Spor :=
  Inputs273.input27_3Spor_of_data sporadicLocalOneData_holds h
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds sporadicMultipliers_holds

theorem primePower_eq_two_three {q : TauCeti.PrimePower} (h : q.card = 8) : q.p = 2 ∧ q.exponent = 3 := by
  have h' : q.p ^ q.exponent = 2 ^ 3 := by rw [← TauCeti.PrimePower.card_def, h]; norm_num
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  rw [hm] at h'
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj q.prime_p Nat.prime_two h'
  exact ⟨h1, by omega⟩

theorem l28AutRank_holds : Inputs273.L28AutRank := by
  intro S _ _ q hv hq8 ⟨e⟩
  have hM := CFSG.Models.lieModel_A 1 q hv e
  obtain ⟨hq2, hq3⟩ := primePower_eq_two_three hq8
  have hBP := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
    (t := .PSL) (by simp [CFSG.Blueprint.classicalTags]) hM
  rw [hq2, hq3] at hBP
  refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_
  have h9 := CFSG.GH74.KGroups.L28.autRank3_le_two hBP E
    ⟨fun a ha b hb => congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩), fun a ha => hE.2 a ha⟩
  norm_num
  exact h9

theorem defCharOuterCoreFree_holds :
    CFSG.HardMathSupport.Dickson.I271.DefCharOuterCoreFree :=
  CFSG.HardMathSupport.Dickson.I271.defCharOuterCoreFree_of_kdata
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCoreFree_holds
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutCentInner_holds

theorem input27_3ChevP_of_L227
    (h : Inputs273.Input27_3L227) : Inputs273.Input27_3ChevP :=
  Inputs273.input27_3ChevP_of CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
    defCharOuterCoreFree_holds l28AutRank_holds h

theorem input27_3L227_holds :
    Inputs273.Input27_3L227 :=
  Inputs273.input27_3L227_of CFSG.HardMathSupport.Solomon.Coordinator.l2CentreThree_holds

theorem input27_3ChevP_holds :
    Inputs273.Input27_3ChevP :=
  input27_3ChevP_of_L227 input27_3L227_holds

theorem input27_4ChevP_of_up
    (h : Inputs273.Input27_4L227Up) : Inputs273.Input27_4ChevP :=
  Inputs273.input27_4ChevP_of CFSG.HardMathSupport.Solomon.Coordinator.l2CentreThree_holds
    Inputs196.input19_6_4_holds (fun p hp hp2 => PumpDefChar.kdChevDownQ_odd hp hp2 p) h

theorem input27_4L227Up_holds :
    Inputs273.Input27_4L227Up :=
  Inputs273.input27_4L227Up_of
    (CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of Nat.prime_three (by norm_num)
      (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds Nat.prime_three (by norm_num))
      (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds Nat.prime_three (by norm_num)
        CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable))
    (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds Nat.prime_three (by norm_num)
      CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable)
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds

theorem input27_4ChevP_holds :
    Inputs273.Input27_4ChevP :=
  input27_4ChevP_of_up input27_4L227Up_holds

theorem input27_3Alt_of_two (h : Inputs273.Input27_3AltRegularTwo) :
    Inputs273.Input27_3Alt :=
  Inputs273.input27_3Alt_of_regular (Inputs273.input27_3AltRegular_of_two Inputs129.input23_5_holds h)

theorem input27_3Core_of_residuals
    (hAlt : Inputs273.Input27_3AltRegularTwo) (hCube : Inputs273.SporOneBalanceCube)
    (hQ : Inputs273.Input27_3ChevQ) : Inputs27.Input27_3Core :=
  Inputs273.input27_3Core_of_cases (input27_3Alt_of_two hAlt) input27_3ChevP_holds (input27_3Spor_of_cube hCube) hQ

@[expose] def Input27_34Rest : Prop :=
  Inputs273.Input27_3AltRegularTwo ∧ Inputs273.SporOneBalanceCube ∧ Inputs273.Input27_4SporDown ∧
    Inputs273.Input27_3ChevQ ∧ Inputs273.Input27_4ChevQ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273b
