module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzTitsThree

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def D2FreeCaseAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → False

theorem D2FreeCaseAt.indexCaseAt {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop} (h : D2FreeCaseAt i Pp) :
    D2IndexCaseAt i Pp := by
  intro G _ _ _ _ p hp P M A H R _ _ _ Rbar K _ hK he
  exact h _ p hp Rbar _ _ K hK he

theorem d2FreeCaseAt_of_datum {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) → ∀ p, p.Prime → p ≠ 2 →
      Pp p → D2IndexDatum L p) : D2FreeCaseAt i Pp := by
  intro X _ _ p hpc R A X₀ K hK he
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hout, hd⟩ := h K he p hK.prime hK.ne_two hpc
  rcases hd with h2 | h3 | ⟨h3, hgen⟩ | hcore
  · exact h2 (hK.sq_dvd_card hout)
  · exact hK.false_of_three_le_pRank h3
  · exact hK.false_of_fusion_of_card hout h3 hgen
  · exact hK.false_of_core hout hcore

section Tits

theorem d2FreeCaseAt_tits_three (hKF : KFactTitsThreeCore) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1 = .tits) : D2FreeCaseAt (.lie d) fun p => p = 3 := by
  refine d2FreeCaseAt_of_datum fun L _ _ he p _ _ hp => ?_
  subst hp
  obtain ⟨e⟩ := he
  refine ⟨?_, Or.inr (Or.inr (Or.inr (hKF L d hd ⟨e⟩)))⟩
  rw [card_outer_tits_of_mulEquiv d hd e]
  norm_num

end Tits

end CFSG.AGLEmbeddingD2
