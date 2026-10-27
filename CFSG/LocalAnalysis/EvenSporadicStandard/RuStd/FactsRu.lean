module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble

public section

namespace CFSG.EvenSporadicStandard.RuStd

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier

theorem ruFacts_ruP :
    RuFacts ruP where
  card_eq := ruP_card_eq
  card_centralizer := ruP_card_centralizer
  isConj_A := ruP_isConj_A
  isConj_B := ruP_isConj_B
  sq_A := ruP_sq_A
  pair := ruP_pair
  no_256 := ruP_no_256

theorem ruFacts_of_isSporadic
    {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) : RuFacts Y := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  exact ruFacts_ruP.of_mulEquiv e.symm

end CFSG.EvenSporadicStandard.RuStd
