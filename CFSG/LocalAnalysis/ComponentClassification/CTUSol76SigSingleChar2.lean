module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSplit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsCharTwo
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Even

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Assembly.LowTwoRank

@[expose] def OddClassicalRep (S : Type) [Group S] : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧ StatedClassicalModel S t n p f

@[expose] def OddExceptionalRep (S : Type) [Group S] : Prop :=
  (∃ (t : StatedLieTag) (p f : ℕ), p ≠ 2 ∧ t ∈ Blueprint.chevalleyExceptionalTags ∧
      Blueprint.ChevalleyExceptionalModel S t p f) ∨
    ∃ p f : ℕ, Blueprint.ReeTitsModel S .twistedG2 p f

theorem not_isTwoComponentIn_centralizer_of_classical_even {T : Type} [Group T] [Finite T]
    {t : StatedLieTag} {n f : ℕ} (hm : StatedClassicalModel T t n 2 f) {x : T}
    (hx : orderOf x = 2) (Q : Subgroup T) :
    ¬ IsTwoComponentIn Q (centralizer ({x} : Set T)) := by
  intro hQ
  have hC : IsCharacteristicP 2 (centralizer ({x} : Set T)) := by
    cases t with
    | PSL => exact RankTwoClassical.isCharacteristicP_centralizer_of_psl_model hm x hx
    | PSU => exact RankTwoClassical.isCharacteristicP_centralizer_of_psu_model hm x hx
    | PSp => exact RankTwoClassical.isCharacteristicP_centralizer_of_psp_model hm x hx
    | POmegaOdd => exact absurd rfl hm.1.2.2.2
    | POmegaPlus =>
      exact RankTwoClassical.isCharacteristicP_centralizer_of_pOmega_model (Or.inl rfl) hm x hx
    | POmegaMinus =>
      exact RankTwoClassical.isCharacteristicP_centralizer_of_pOmega_model (Or.inr rfl) hm x hx
    | G2 => exact (hm.2 : False).elim
    | F4 => exact (hm.2 : False).elim
    | E6 => exact (hm.2 : False).elim
    | E7 => exact (hm.2 : False).elim
    | E8 => exact (hm.2 : False).elim
    | twistedE6 => exact (hm.2 : False).elim
    | trialityD4 => exact (hm.2 : False).elim
    | twistedB2 => exact (hm.2 : False).elim
    | twistedG2 => exact (hm.2 : False).elim
    | twistedF4 => exact (hm.2 : False).elim
    | Tits => exact (hm.2 : False).elim
  exact Foote5.OddLieCore.Exc.not_isPComponent_two_of_isCharacteristicP hC _ hQ.2

theorem singleComponentSimpleAt_classical_even :
    SingleComponentSimpleAt
      (fun S _ => ∃ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel S t n 2 f) :=
  singleComponentSimpleAt_of_noTwoComponent fun _ _ _ _ ⟨_, _, _, hm⟩ _ hx Q =>
    not_isTwoComponentIn_centralizer_of_classical_even hm hx Q

theorem singleComponentSimpleAt_exceptional_even :
    SingleComponentSimpleAt (fun S _ =>
      (∃ (t : StatedLieTag) (f : ℕ), t ∈ Blueprint.chevalleyExceptionalTags ∧
          Blueprint.ChevalleyExceptionalModel S t 2 f) ∨
        (∃ (p f : ℕ), Blueprint.ReeTitsModel S .twistedF4 p f ∨
          Blueprint.ReeTitsModel S .Tits p f) ∨
        ∃ p f : ℕ, Blueprint.SuzukiModel S p f) :=
  singleComponentSimpleAt_of_noTwoComponent fun _ _ _ _ hP x hx _ hQ =>
    Foote5.OddLieCore.Exc.involutionCentralizersNoTwoComponent_even hP x hx _ hQ.2

theorem classicalRep_even_or_odd {S : Type} [Group S] (h : Milestones.ClassicalRep S) :
    (∃ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel S t n 2 f) ∨ OddClassicalRep S := by
  obtain ⟨t, n, p, f, hm⟩ := h
  by_cases hp : p = 2
  · subst hp
    exact Or.inl ⟨t, n, f, hm⟩
  · exact Or.inr ⟨t, n, p, f, hp, hm⟩

theorem exceptionalRep_even_or_odd {S : Type} [Group S] (h : Blueprint.ExceptionalRep S) :
    ((∃ (t : StatedLieTag) (f : ℕ), t ∈ Blueprint.chevalleyExceptionalTags ∧
          Blueprint.ChevalleyExceptionalModel S t 2 f) ∨
        (∃ (p f : ℕ), Blueprint.ReeTitsModel S .twistedF4 p f ∨
          Blueprint.ReeTitsModel S .Tits p f) ∨
        ∃ p f : ℕ, Blueprint.SuzukiModel S p f) ∨ OddExceptionalRep S := by
  rcases h with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
  · by_cases hp : p = 2
    · subst hp
      exact Or.inl (Or.inl ⟨t, f, ht, hm⟩)
    · exact Or.inr (Or.inl ⟨t, p, f, hp, ht, hm⟩)
  · have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      simpa [Blueprint.reeTitsTags] using ht
    rcases ht' with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨p, f, hm⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨p, f, Or.inl hm⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨p, f, Or.inr hm⟩))
  · exact Or.inl (Or.inr (Or.inr ⟨p, f, hm⟩))

end CFSG.ComponentClassification.Sol76.Sig
