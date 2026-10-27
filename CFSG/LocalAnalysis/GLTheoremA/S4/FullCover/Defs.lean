module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def CoverListed : TauCeti.CFSGIndex → Prop
  | .lie i =>
    match i.1 with
    | .A 2 _ => True
    | .twistedA 2 _ => True
    | .twistedA 5 q => q.card = 2
    | _ => False
  | i => k2HatIndex 3 i ∨ k3HatIndex 3 i

@[expose] def ListedMultiplierBound (p : ℕ) : Prop :=
  ∀ i : TauCeti.CFSGIndex, (k2 p i ∨ k3 p i) →
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ π : Q →* i.Group, Function.Surjective π → π.ker = Subgroup.center Q →
    IsPGroup p (Subgroup.center Q) → Subgroup.center Q ≠ ⊥ →
      p = 3 ∧ Nat.card (Subgroup.center Q) = 3 ∧ CoverListed i

@[expose] def HatOddMultiplierBound : Prop :=
  ∀ i : TauCeti.CFSGIndex, (k2HatIndex 3 i ∨ k3HatIndex 3 i) →
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ π : Q →* i.Group, Function.Surjective π → π.ker = Subgroup.center Q →
      Odd (Nat.card (Subgroup.center Q)) → Nat.card (Subgroup.center Q) ∣ 3

end CFSG.LocalAnalysis.GLTheoremA
