module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.BasicSec

public section

namespace CFSG.EvenSporadicStandard.Induction

@[expose] def Sol78PredS (S : List TauCeti.SporadicName) (H : Type) [Group H] [Finite H] : Prop :=
  ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ L : Subgroup H, SolStd L → (∃ s ∈ S, OddCover s L) → Sol78Concl N L

theorem Sol78PredS.mono {S T : List TauCeti.SporadicName} (hST : ∀ s ∈ S, s ∈ T) {H : Type}
    [Group H] [Finite H] (h : Sol78PredS T H) : Sol78PredS S H :=
  fun N hN hidx hkp L hL ⟨s, hs, hcov⟩ => h N hN hidx hkp L hL ⟨s, hST s hs, hcov⟩

theorem BelowSec.mono_types {S T : List TauCeti.SporadicName} (hST : ∀ s ∈ S, s ∈ T) {H : Type}
    [Group H] [Finite H] (h : BelowSec (Sol78PredS T) H) : BelowSec (Sol78PredS S) H :=
  ⟨h.uHered, fun _ _ _ hX hlt => (h.apply hX hlt).mono hST⟩

end CFSG.EvenSporadicStandard.Induction
