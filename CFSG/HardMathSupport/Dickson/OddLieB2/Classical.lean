module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.Yardstones.Md42047359a2a.Definitions
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.OddLieB2

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.CatLeaf
open CFSG.Models (LieModel NamesTag)
open TauCeti

private theorem not_namesTag_of_classical {d : LieTypeIndex} {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus) :
    ¬ NamesTag d t p f := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> cases d <;> exact id

private theorem classicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by decide) :
    StatedClassicalModel G t n p f :=
  h.2.resolve_right fun ⟨_, _, hd, _⟩ => not_namesTag_of_classical ht hd

theorem fixedTwoComponentsQuasisimple_of_classical (idx : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.linearUnitary ∨
      CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal)
    (hchar : idx.1.characteristic ≠ 2) (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) :
    CFSG.ComponentClassification.CatLeaf.FixedTwoComponentsQuasisimple S := by
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    have hcl := classicalModel_of_lieModel (CFSG.Models.lieModel_A r q hv e)
    have hp2 : q.p ≠ 2 := by simpa using hchar
    have hn : 2 ≤ r + 1 := hcl.1.2.2.1
    rcases (show r + 1 = 2 ∨ 3 ≤ r + 1 by omega) with h2 | h3
    · rw [h2] at hcl
      exact fixedTwoComponentsQuasisimple_psl_two hnc hp2 hcl
    · exact fixedTwoComponentsQuasisimple_psl hp2 h3 hcl
  | twistedA r q =>
    have hcl := classicalModel_of_lieModel (CFSG.Models.lieModel_twistedA r q hv e)
    exact fixedTwoComponentsQuasisimple_psu hchar hcl
  | B r q =>
    have hp2 : q.p ≠ 2 := by simpa using hchar
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · exact fixedTwoComponentsQuasisimple_psp hp2 (classicalModel_of_lieModel h)
    · exact fixedTwoComponentsQuasisimple_orthogonal (Or.inl rfl) hp2 (classicalModel_of_lieModel h)
  | C r q =>
    exact fixedTwoComponentsQuasisimple_psp (show q.p ≠ 2 by simpa using hchar)
      (classicalModel_of_lieModel (CFSG.Models.lieModel_C r q hv e))
  | D r q =>
    exact fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inl rfl))
      (show q.p ≠ 2 by simpa using hchar)
      (classicalModel_of_lieModel (CFSG.Models.lieModel_D r q hv e))
  | twistedD r q =>
    exact fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inr rfl))
      (show q.p ≠ 2 by simpa using hchar)
      (classicalModel_of_lieModel (CFSG.Models.lieModel_twistedD r q hv e))
  | E6 _ | E7 _ | E8 _ | F4 _ | G2 _ | twistedE6 _ | trialityD4 _ | suzuki _ | reeG2 _
  | reeF4 _ | tits =>
    exfalso
    rcases hfam with h | h <;> simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at h

end CFSG.HardMathSupport.Dickson.OddLieB2
