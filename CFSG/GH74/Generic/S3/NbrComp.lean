module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.S3.NbrR

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def NbrCompAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K → IsComponent (S45.barSub y Iv) → IsCompC Iv y

@[expose] def B_S3_nbrComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K → NbrCompAt x K

end CFSG.GH74.Generic.S3
