module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Models.Transport
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType


@[expose] def RestIndex : TauCeti.LieTypeIndex → Prop
  | .B n q => 2 ≤ n ∧ q.p = 2
  | .C n q => 2 ≤ n ∧ q.p = 2
  | .D n q => 5 ≤ n ∧ q.p = 2
  | .twistedD n q => 4 ≤ n ∧ q.p = 2
  | .G2 q => q.p = 2
  | .F4 q => q.p = 2
  | .E6 q => q.p = 2
  | .twistedE6 q => q.p = 2
  | .E7 q => q.p = 2
  | .E8 q => q.p = 2
  | .trialityD4 q => q.p = 2
  | .suzuki m => 1 ≤ m
  | .reeF4 m => 1 ≤ m
  | _ => False

theorem innAutDerivedInnDiag_rest : InnAutDerivedInnDiag RestIndex := by
  intro Γ _ _ p J a haJ hp hq hcat hmem
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | A n q => exact hi.elim
    | twistedA n q => exact hi.elim
    | B n q =>
      obtain ⟨hn, hq2⟩ := hi
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .PSp n 2 q.exponent := by
        rcases CFSG.Models.lieModel_B n q hv e with h | h
        · rw [hq2] at h
          exact CFSG.Models.LieModel.toBlueprint (by decide) h
        · exfalso
          exact h.1.2.2.2 hq2
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | C n q =>
      obtain ⟨hn, hq2⟩ := hi
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
      exact absurd hq2 hr.2
    | D n q =>
      obtain ⟨hn, hq2⟩ := hi
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .POmegaPlus n 2 q.exponent := by
        have h := CFSG.Models.lieModel_D n q hv e
        rw [hq2] at h
        exact CFSG.Models.LieModel.toBlueprint (by decide) h
      refine innDiagOn_of_lieModel haJ hq hLM ?_ (by decide) hmem
      rintro ⟨-, h4⟩
      omega
    | twistedD n q =>
      obtain ⟨hn, hq2⟩ := hi
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .POmegaMinus n 2 q.exponent := by
        have h := CFSG.Models.lieModel_twistedD n q hv e
        rw [hq2] at h
        exact CFSG.Models.LieModel.toBlueprint (by decide) h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | G2 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .G2 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_G2 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | F4 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .F4 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | E6 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .E6 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | E7 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .E7 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | E8 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .E8 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | twistedE6 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .twistedE6 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | trialityD4 q =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .trialityD4 0 2 q.exponent := by
        have h := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_trialityD4 q hv e
        rw [hi] at h
        exact h
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | suzuki m =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .twistedB2 0 2 (2 * m + 1) :=
        CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_suzuki m hv e
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | reeG2 m => exact hi.elim
    | reeF4 m =>
      have hLM : CFSG.Blueprint.LieModel (PSimple p J) .twistedF4 0 2 (2 * m + 1) :=
        CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_reeF4 m hv e
      exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem
    | tits => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
