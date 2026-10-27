module

public import CFSG.GH74.GLS.C3.Layer1.St1Defs
public import CFSG.GH74.GLS.C3.Statements

public section

namespace CFSG.GH74.GLS

@[expose] def B_st1_thm7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G

@[expose] def B_st1_prop41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G

@[expose] def B_st1_prop51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G → St1Prop51 G

@[expose] def B_st1_thm4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Prop51 G → St1Thm4 G

@[expose] def B_st1_thm5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Thm4 G → St1Thm5 G

@[expose] def B_st1_thm6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Prop51 G → St1Thm5 G → St1Thm6 G

end CFSG.GH74.GLS
