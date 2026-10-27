module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

public section

namespace CFSG.EvenSporadicStandard.HNRecog

structure SqFacts : Prop where
  exists_sq : ∃ g : ↥P1408, g ^ 2 = pA
  isConj_sq : ∀ {g g' : ↥P1408}, g ^ 2 = pA → g' ^ 2 = pA → IsConj g g'
  card_cent : ∀ {g : ↥P1408}, g ^ 2 = pA →
    Nat.card ↥(Subgroup.centralizer ({g} : Set ↥P1408)) = 5760

end CFSG.EvenSporadicStandard.HNRecog
