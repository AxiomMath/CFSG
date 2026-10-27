module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.EvenArm
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKill

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (RankTwoStdRec)

@[expose] def RuPerfectCentralizer : Prop :=
  ∀ {R : Type} [Group R], IsSporadic R .Ru → ∀ {u : R}, orderOf u = 2 →
    ∀ {X : Subgroup R}, Group.IsPerfect ↥X → (∀ x ∈ X, x * u = u * x) →
      29120 ∣ Nat.card ↥X → Nat.card ↥X = 29120

@[expose] def ExcInput : Prop :=
  ∀ {Y : Type} [Group Y], Thm54Order (Nat.card Y) →
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException Y

structure CatInputs : Prop where
  arm : CFSG.ComponentClassification.CatFC.ArmInputs
  cardAll : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s
  even : EvenArmInputs
  ru : RuPerfectCentralizer

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
