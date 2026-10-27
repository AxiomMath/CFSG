module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.NonA

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti

@[expose] def SmallPSp45 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 5 → d.1 = .B 2 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallPSp47 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 7 → d.1 = .B 2 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallOmega73 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .B 3 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallPSp63 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .C 3 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallPSp83 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .C 4 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallU43 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .twistedA 3 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallU53 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .twistedA 4 q →
    NoFFModule (CFSGIndex.lie d).Group

@[expose] def SmallG23 : Prop :=
  ∀ (d : ValidLieTypeIndex) (q : PrimePower), q.card = 3 → d.1 = .G2 q →
    NoFFModule (CFSGIndex.lie d).Group

theorem gf2NoFFLieOddSmall_of_cells (h1 : SmallPSp45) (h2 : SmallPSp47) (h3 : SmallOmega73)
    (h4 : SmallPSp63) (h5 : SmallPSp83) (h6 : SmallU43) (h7 : SmallU53) (h8 : SmallG23) :
    GF2NoFFLieOddSmall := by
  intro d hd _
  rcases hd with ⟨q, h57, hq⟩ | ⟨q, hq3, hq⟩
  · rcases h57 with h | h
    · exact h1 d q h hq
    · exact h2 d q h hq
  · rcases hq with hq | hq | hq | hq | hq | hq
    · exact h3 d q hq3 hq
    · exact h4 d q hq3 hq
    · exact h5 d q hq3 hq
    · exact h6 d q hq3 hq
    · exact h7 d q hq3 hq
    · exact h8 d q hq3 hq

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
