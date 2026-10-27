module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.SeitzReduction

theorem lieModel_of_isD42 {G : Type} [Group G] (h : IsCatalogLieIso G IsD42Index) :
    LieModel G .POmegaPlus 4 2 1 := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, hf⟩ := hd
    simpa only [hp, hf] using blueprintLieModel_D 4 q hv e
  | _ => exact hd.elim

theorem classical_type_of_isD42 {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (ht : t ∈ classicalTags) (hG : LieModel G t n 2 f)
    (hD : IsCatalogLieIso G IsD42Index) : t = .POmegaPlus ∧ n = 4 ∧ f = 1 := by
  have hD' := lieModel_of_isD42 hD
  refine OmegaPilot.evenLieOrder_eq_POmega (Or.inl rfl)
    (F4Pilot.statedLieAdmissible_of_lieModel hG) (by decide) (by decide) ?_
  rw [← F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags ht hG,
    ← OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hD']

theorem statedClassicalModel_of_isOmegaTwoBig {G : Type} [Group G]
    (h : IsCatalogLieIso G IsOmegaTwoBigIndex) :
    ∃ t n, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 5 ≤ n ∧ StatedClassicalModel G t n 2 1 := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | D r q =>
    obtain ⟨hr, hp, hf⟩ := hd
    have hlm := blueprintLieModel_D r q hv e
    rw [hp, hf] at hlm
    exact ⟨.POmegaPlus, r, Or.inl rfl, hr,
      CFSG.GH74.statedClassicalModel_of_lieModel (by omega) hlm⟩
  | twistedD r q =>
    obtain ⟨hr, hp, hf⟩ := hd
    have hlm := blueprintLieModel_twistedD r q hv e
    rw [hp, hf] at hlm
    exact ⟨.POmegaMinus, r, Or.inr rfl, hr,
      CFSG.GH74.statedClassicalModel_of_lieModel (by omega) hlm⟩
  | _ => exact hd.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
