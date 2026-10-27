module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Z0Inv
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Kappa

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Steps


@[expose] def StepZ0Inv : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → d.S56Z0Inv

@[expose] def StepKappa : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → d.S56Kappa

@[expose] def Step05 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node05 d z₀

@[expose] def Step07 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → Node07 d

@[expose] def Step08 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Z0Inv → Node05 d z₀ → Node06 d z₀ → Node07 d →
      Node08 d z₀

@[expose] def Step09 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Kappa → Node05 d z₀ → Node07 d → Node08 d z₀ →
      Node09 d z₀

@[expose] def Step10 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Z0Inv → Node05 d z₀ → Node06 d z₀ → Node07 d →
      Node08 d z₀ → Node09 d z₀ → Node10 d z₀

@[expose] def Step11 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node05 d z₀ → Node07 d → Node08 d z₀ → Node09 d z₀ →
      Node10 d z₀ → Node11 d z₀

@[expose] def Step12 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Z0Inv → Node06 d z₀ → Node09 d z₀ → Node10 d z₀ →
      Node11 d z₀ → Node12 d z₀

@[expose] def Step13 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node07 d → Node08 d z₀ → Node10 d z₀ → Node11 d z₀ →
      Node12 d z₀ → Node13 d

@[expose] def Step14 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node10 d z₀ → Node11 d z₀ → Node12 d z₀ → Node13 d →
      Node14 d

@[expose] def Step15 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node10 d z₀ → Node15 d z₀

@[expose] def Step17s : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node05 d z₀ → Node09 d z₀ → Node10 d z₀ → Node17s d z₀

@[expose] def Step16 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node10 d z₀ → Node12 d z₀ → Node14 d →
      Node15 d z₀ → Node17s d z₀ → Node16 d z₀

@[expose] def Step17 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node10 d z₀ → Node14 d → Node15 d z₀ →
      Node16 d z₀ → Node17s d z₀ → Node17 d z₀

@[expose] def Step18 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Kappa → Node09 d z₀ → Node10 d z₀ → Node14 d →
      Node17s d z₀ → Node17 d z₀ → Node18 d

@[expose] def Step19 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node10 d z₀ → Node14 d → Node17s d z₀ →
      Node17 d z₀ → Node18 d → Node19 d z₀

@[expose] def Step19b : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node19b d z₀

@[expose] def Step20 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node14 d → Node17s d z₀ → Node17 d z₀ →
      Node18 d → Node19 d z₀ → Node20 d z₀

@[expose] def Step21 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node19 d z₀ → Node19b d z₀ → Node20 d z₀ →
      Node21 d z₀

@[expose] def Step22 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node14 d → Node17s d z₀ → Node17 d z₀ → Node19 d z₀ →
      Node20 d z₀ → Node21 d z₀ → Node22 d z₀

@[expose] def Step23a : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Z0Inv → Node10 d z₀ → Node14 d → Node16 d z₀ →
      Node17s d z₀ → Node17 d z₀ → Node19 d z₀ → Node20 d z₀ → Node21 d z₀ → Node22 d z₀ →
        Node23a d z₀

@[expose] def Step23b : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → d.S56Z0Inv → Node10 d z₀ → Node14 d → Node17 d z₀ →
      Node19 d z₀ → Node23a d z₀ → Node23b d z₀

@[expose] def Step23c : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node10 d z₀ → Node14 d → Node17s d z₀ → Node17 d z₀ →
      Node19 d z₀ → Node20 d z₀ → Node21 d z₀ → Node23a d z₀ → Node23b d z₀ → Node23c d z₀

@[expose] def Step24 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node07 d → Node10 d z₀ → Node11 d z₀ → Node12 d z₀ → Node13 d →
      Node14 d → Node16 d z₀ → Node19 d z₀ → Node20 d z₀ → Node21 d z₀ → Node22 d z₀ → Node23a d z₀ →
        Node23b d z₀ → Node23c d z₀ → Node24 d

@[expose] def Step25 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node09 d z₀ → Node17 d z₀ → Node19 d z₀ → Node20 d z₀ →
      Node21 d z₀ → Node22 d z₀ → Node24 d → Node25 d z₀

@[expose] def Step26 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G},
    d.Thm49Statement → d.Hyp → d.S56Z0 z₀ → Node22 d z₀ → Node23a d z₀ → Node25 d z₀ → Node26 d z₀

end Steps

end CFSG.LocalAnalysis.EvenBN.Tits.N
