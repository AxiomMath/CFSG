module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22EvenCoverProved

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census

section Atlas


structure FiAtlasRest : Prop where
  fi22Covers : Fi22CoversFixesElem
  u62Covers : U62CoversFixesElem
  fi22U62 : Fi22U62Sub
  u62Odd : U62OddExclHered

theorem FiAtlasRest.toAtlas
    (r : FiAtlasRest) (hSM : SporadicMultipliers) : FiAtlas where
  fi22Covers := r.fi22Covers
  u62Covers := r.u62Covers
  fi22Even := fi22EvenCover_proved hSM
  fi22U62 := r.fi22U62
  u62Odd := r.u62Odd

end Atlas

end CFSG.EvenSporadicStandard.Induction.Fi
