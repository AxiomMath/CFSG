module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def FiStage3 : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi24Prime →
        ∀ L : Subgroup H, SolStd L → (∃ s ∈ fiTypes, OddCover s L) →
          ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
            FiOut H N L' s'

@[expose] def FiSmallFStar : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    (IsSporadic ↥N .Fi22 ∨ IsSporadic ↥N .Fi23) →
      ∀ (L : Subgroup H) (s : TauCeti.SporadicName), s ∈ fiTypes → SolStd L → OddCover s L → False

@[expose] def FiStage3Main : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime →
          ∀ L : Subgroup H, SolStd L → (∃ s ∈ fiTypes, OddCover s L) →
            ∃ (s' : TauCeti.SporadicName) (L' : Subgroup H), s' ∈ fiTypes ∧ OddCover s' L' ∧
              FiOut H N L' s'

theorem fiStage3_of_main (hsmall : FiSmallFStar) (hmain : FiStage3Main) : FiStage3 := by
  intro lit H _ _ ih N hN hidx hkp hN24 L hL ⟨s, hs, hcov⟩
  by_cases h : IsSporadic ↥N .Fi22 ∨ IsSporadic ↥N .Fi23
  · exact (hsmall H N hN hidx h L s hs hL hcov).elim
  · push Not at h
    exact hmain lit H ih N hN hidx hkp h.1 h.2 hN24 L hL ⟨s, hs, hcov⟩

theorem exists_noBiggerFi {H : Type} [Group H] {L : Subgroup H} {s : TauCeti.SporadicName}
    (hs : s ∈ fiTypes) (hL : SolStd L) (hcov : OddCover s L) :
    ∃ (s₀ : TauCeti.SporadicName) (L₀ : Subgroup H), s₀ ∈ fiTypes ∧ SolStd L₀ ∧ OddCover s₀ L₀ ∧
      NoBiggerFi H s₀ ∧ Nat.card (Carrier s) ≤ Nat.card (Carrier s₀) := by
  classical
  let P : TauCeti.SporadicName → Prop := fun s₁ => s₁ ∈ fiTypes ∧ ∃ L₁ : Subgroup H, SolStd L₁ ∧
    OddCover s₁ L₁
  have hne : (fiTypes.toFinset.filter P).Nonempty := ⟨s, by simp [P, hs]; exact ⟨L, hL, hcov⟩⟩
  obtain ⟨s₀, hs₀, hmax⟩ := Finset.exists_max_image (fiTypes.toFinset.filter P)
    (fun s₁ => Nat.card (Carrier s₁)) hne
  obtain ⟨hs₀t, hs₀P⟩ := Finset.mem_filter.1 hs₀
  obtain ⟨hs₀f, L₀, hL₀, hcov₀⟩ : s₀ ∈ fiTypes ∧ ∃ L₁ : Subgroup H, SolStd L₁ ∧ OddCover s₀ L₁ :=
    hs₀P
  refine ⟨s₀, L₀, hs₀f, hL₀, hcov₀, fun L₁ s₁ hL₁ hs₁ hcov₁ => ?_, ?_⟩
  · exact hmax s₁ (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hs₁, hs₁, L₁, hL₁, hcov₁⟩)
  · exact hmax s (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hs, hs, L, hL, hcov⟩)

theorem fi_case (h3 : FiStage3) (lit : Sol78Lit) (hclose : Sol78ClosingFi) (hgiven : FiGiven)
    (H : Type) [Group H] [Finite H] (ih : BelowSec (Sol78PredS fiTypes) H) (N : Subgroup H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (L : Subgroup H) (hL : SolStd L)
    (s : TauCeti.SporadicName) (hs : s ∈ fiTypes) (hcov : OddCover s L) : Sol78Concl N L := by
  by_cases hN24 : IsSporadic ↥N .Fi24Prime
  · exact ⟨(hgiven H N L s hs hN hN24 hidx hkp hL hcov).1, hN24⟩
  · obtain ⟨s', L', hs', hcov', hout⟩ := h3 lit H ih N hN hidx hkp hN24 L hL ⟨s, hs, hcov⟩
    exact absurd (hclose lit H ih N L' s' hs' hN hidx hkp hcov' hout).2 hN24

theorem step_fi (h3 : FiStage3) (lit : Sol78Lit) (hclose : Sol78ClosingFi) (hgiven : FiGiven) :
    StepSec (Sol78PredS fiTypes) :=
  fun H _ _ ih N hN hidx hkp L hL ⟨s, hs, hcov⟩ =>
    fi_case h3 lit hclose hgiven H ih N hN hidx hkp L hL s hs hcov

end CFSG.EvenSporadicStandard.Induction
