module

public import CFSG.Timmesfeld.Assembly

public section

namespace CFSG.CGT.T75E

open CFSG.Timmesfeld CFSG.Blueprint

theorem arsHyp_or_exc_at {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hL : (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
      RootClosure D ∧ SpecialClosure D ∧ RootMoufang D)
    (hX : (∀ d ∈ D, rootSet D d = {d}) →
      (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
      Moufang.CommLambda D ∧ Moufang.LL5 D ∧ Moufang.NoPolar D)
    (hconn : Moufang.NoPolar D → Closure.CommConnected D) :
    ARS.Hyp G (rootClass D) ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2 := by
  by_cases hlarge : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  · obtain ⟨hc, hs, hm⟩ := hL hlarge
    exact Or.inl (arsHyp_rootClass h hc hs hm)
  · push Not at hlarge
    have hsing : ∀ d ∈ D, rootSet D d = {d} := fun d hd =>
      rootSet_eq_singleton_of_forall hlarge hd
    by_cases hex : ∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧
        orderOf (d * c) ≠ 3
    · obtain ⟨hQ, hLL, hNP⟩ := hX hsing hex
      rcases Moufang.exceptionalInput_at h hsing hex
          ⟨hQ, hLL, hNP, Moufang.lineCount_of h hsing hQ hLL hNP (hconn hNP)⟩ (hconn hNP)
          Moufang.a6Endgame Moufang.j2Endgame with he | hj
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr hj)
    · push Not at hex
      exact Or.inl (arsHyp_rootClass h (rootClosure_of_singleton hsing)
        (specialClosure_of_singleton h.root hsing) (Moufang.rootMoufang_of_singleton hsing hex))

theorem key_of_stepsSE_NJ2 (hL : Bridge.LargeStepSE) (hX : Moufang.ExceptionalGlobalStepNJ2)
    (hconn : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Moufang.NoPolar D →
      Closure.CommConnected D)
    (hA : ARSInput) : ∀ n : ℕ, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      Outcome G ∧ ((∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
        RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ Bridge.ExistsCommSpec D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn h
    have IH : Bridge.RootIHStructE G := fun G' _ D' h' hlt => ih _ (hn ▸ hlt) G' D' rfl h'
    refine ⟨?_, hL G D h IH⟩
    by_cases hJ : NativeSporadic.IsSporadic G .J2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))))
    · refine outcome_at h (fun hl => ?_)
        (fun hsing hex => hX G D h IH.toStruct.rootIH hsing hex hJ) (hconn G D h) hA
      obtain ⟨hc, hs, hm, _⟩ := hL G D h IH hl
      exact ⟨hc, hs, hm⟩


theorem arsHyp_or_exc_of_hyp {G : Type} [Group G] {D : Set G} (hH : Hyp G D) :
    ARS.Hyp G (rootClass D) ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2 := by
  have hT : Moufang.Tim75Thm31 := Bridge.tim75Thm31
  have hK : Bridge.ThirdKindStep :=
    Bridge.RootClosure.thirdKindStep_of_rootThreeL2 Bridge.commonNeighbour hT
      (Bridge.RootClosure.rootThreeL2Stmt_of Bridge.RootClosure.psl2SylowCoordStmt
        Bridge.RootClosure.l2TorusIrredStmt Bridge.RootClosure.naturalComplementStmt)
  have hI : OpenInputs := openInputs_holds
  have hL : Bridge.LargeStepSE :=
    Bridge.largeStepSE_of_third hK Bridge.gammaResidualStep
      (Bridge.commLambdaStep_of_nCore (Bridge.nCoreStep_of_nCoreStepLarge Bridge.nCoreStepLarge))
      (Bridge.existsCommSpecStepE_of_thin hT Bridge.nCoreStepLarge
        (Bridge.thinOneOppositeStepE_of_split
          (Bridge.thinManyStepE_of Bridge.rootLinesPowerStep Bridge.rootLinesTorusStep
            (Bridge.thinGateManyStep_of
              (Bridge.thinGateCoreStep_of
                (Bridge.thinGateCoreSmallStep_of Bridge.thinGateCenterStep Bridge.thinGateIrrStep)
                Bridge.thinGateCoreOneStep))
            (Bridge.RootOne.thinGateOneStep_of Bridge.thinGateOne_kOne))
          (Bridge.thinTwoStepE_of_thinAllBadFalse hI.thinAllBadFalse)))
  have hX : Moufang.ExceptionalGlobalStepNJ2 :=
    Moufang.exceptionalGlobalStepNJ2_of_noPlane (Moufang.exceptionalNoPlaneStepNJ2_of_cases
      (Moufang.exceptionalLeviStep_of_tim75 hT Bridge.caseICommPQInput_holds)
      Bridge.exceptionalNoLeviPlaneStep_holds
      (Moufang.exceptionalNoLeviTO5StepNJ2_of_diam4
        (Moufang.excDiam4InputNJ2_of Moufang.Deep.excThreeNearInput hI.exceptionalCyc)))
  have hconn : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Moufang.NoPolar D →
      Closure.CommConnected D := fun _ _ _ hH' hNP =>
    Bridge.commConnected_of_noPolar
      (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) hH' hNP
  have key := key_of_stepsSE_NJ2 hL hX hconn arsInput
  have IH : Bridge.RootIHStructE G := fun G' _ D' h' hlt => key _ G' D' rfl h'
  by_cases hJ : NativeSporadic.IsSporadic G .J2
  · exact Or.inr (Or.inr hJ)
  · refine arsHyp_or_exc_at hH (fun hl => ?_)
      (fun hsing hex => hX G D hH IH.toStruct.rootIH hsing hex hJ) (hconn G D hH)
    obtain ⟨hc, hs, hm, _⟩ := hL G D hH IH hl
    exact ⟨hc, hs, hm⟩

end CFSG.CGT.T75E
