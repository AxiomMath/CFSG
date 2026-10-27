module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSp4
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecExc
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecM11
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecRee

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def LinearExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedClassicalModel ↥(generalizedFitting H) .PSL n p f → False

@[expose] def UnitaryExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedClassicalModel ↥(generalizedFitting H) .PSU n p f → False

@[expose] def SymplecticExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (n p f : ℕ), p.Prime → p ≠ 2 → 3 ≤ n →
    StatedClassicalModel ↥(generalizedFitting H) .PSp n p f → False

@[expose] def OrthogonalExclusion : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Config H) (t : StatedLieTag) (n p f : ℕ), p.Prime →
    p ≠ 2 → (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
    StatedClassicalModel ↥(generalizedFitting H) t n p f → False

theorem cfSp4RecognitionCI_of_classical (hL : LinearExclusion) (hU : UnitaryExclusion)
    (hS : SymplecticExclusion) (hO : OrthogonalExclusion) : GSThmB.CFSp4RecognitionCI := by
  intro H _ _ h hType hB hKa hZK hJ
  obtain ⟨c, hcJ⟩ := Config.exists_ofHyp59 h hB hKa hZK hJ
  rcases hType with hodd | hM11
  · obtain ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩ := hodd
    rcases hmodel with ⟨htc, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
    · cases t with
      | PSL => exact (hL H c n p f hp hp2 hcl).elim
      | PSU => exact (hU H c n p f hp hp2 hcl).elim
      | PSp =>
        by_cases hn : n = 2
        · subst hn
          have hLie : LieModel ↥(generalizedFitting H) .PSp 2 p f := Or.inl ⟨htc, hcl⟩
          refine ⟨p, f, hp, hp2, hadm.2.1, hLie, ?_⟩
          exact LieType.CurtisTits.lieModel_of_mulEquiv
            (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (MulEquiv.subgroupCongr hcJ))
            (c.lieModel_J_of_psp hp2 hLie)
        · exact (hS H c n p f hp hp2 (by have := hadm.2.2.1; omega) hcl).elim
      | POmegaOdd => exact (hO H c _ n p f hp hp2 (Or.inl rfl) hcl).elim
      | POmegaPlus => exact (hO H c _ n p f hp hp2 (Or.inr (Or.inl rfl)) hcl).elim
      | POmegaMinus => exact (hO H c _ n p f hp hp2 (Or.inr (Or.inr rfl)) hcl).elim
      | _ => exact hcl.2.elim
    · exact (c.false_of_exceptional hp2 hex).elim
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact (c.false_of_ree hree).elim
      · exact absurd hree.1.2.2.2.1 hp2
      · exact absurd hree.1.2.2.2.1 hp2
    · exact absurd hsz.1 hp2
  · exact (c.false_of_M11 hM11).elim

end CFSG.ComponentClassification.Sp4Rec
