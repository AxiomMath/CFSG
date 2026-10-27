module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Pt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericPrimeThreeL28Lemma42 (G : Type) [Group G] [Finite G] : Prop :=
  GenericL28At G fun p P M x J => L28Prop34 p P J x → L28PointLemma42 p P M x

end CFSG.LocalAnalysis.RankThreeTheoremC
