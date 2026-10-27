module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericPrimeThreeA6Prop34 (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P _ x J => A6Prop34 p P J x

@[expose] def GL83GenericPrimeThreeA6Lemma43 (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P M x J => A6Prop34 p P J x → A6PointLemma43 p P M J x

theorem GL83GenericPrimeThreeTypes2.of_a6_l28 (hA : GL83GenericPrimeThreeA6 G)
    (hL : GL83GenericPrimeThreeL28 G) : GL83GenericPrimeThreeTypes2 G :=
  hA.union hL

end CFSG.LocalAnalysis.RankThreeTheoremC
