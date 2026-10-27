module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard

@[expose] def EvenCoverOutAt (Up : List TauCeti.SporadicName) (s' : TauCeti.SporadicName)
    (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ L' : Subgroup Y, SolStd L' →
      CFSG.IsQuasisimple ↥L' → IsSporadic (↥L' ⧸ center ↥L') s' →
        ¬ Odd (Nat.card ↥(center ↥L')) → ∃ s'' ∈ Up, IsSporadic ↥N' s''

@[expose] def EvenCoverOutHered (Up : List TauCeti.SporadicName) (s' : TauCeti.SporadicName) :
    Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → EvenCoverOutAt Up s' Y

@[expose] def EvenCoverExclHered (s' : TauCeti.SporadicName) : Prop := EvenCoverOutHered [] s'

theorem EvenCoverOutHered.mono {Up Up' : List TauCeti.SporadicName} (h : ∀ s ∈ Up, s ∈ Up')
    {s' : TauCeti.SporadicName} (hs : EvenCoverOutHered Up s') : EvenCoverOutHered Up' s' :=
  fun Y _ _ hY N' hN hidx hkp L' hsol hq hcq hodd => by
    obtain ⟨s'', hs'', hN'⟩ := hs Y hY N' hN hidx hkp L' hsol hq hcq hodd
    exact ⟨s'', h s'' hs'', hN'⟩

end CFSG.EvenSporadicStandard.Induction
