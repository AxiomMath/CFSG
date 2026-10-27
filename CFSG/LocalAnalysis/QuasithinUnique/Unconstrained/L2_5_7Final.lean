module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7End

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

structure Inputs257 : Prop where
  borel : RankTwoBorelFacts
  nonIso : NonIso257
  p121 : Id2519.Prop121Three
  geom : RankTwoGeom257
  maxRank : RankTwoMaxRank257
  cover : Cover257a
  torus : RankTwoTorus257
  autOdd : AutOdd257

theorem lemma257_of_inputs (h : Inputs257) : Lemma257 := by
  intro G _ _ T M hs N hlv n hmodel
  by_contra hn1
  have hn2 : 2 ≤ n := by
    rcases hmodel with hm | hm
    · have h1 : 1 ≤ n := hm.1.2.1
      omega
    · have h1 : 1 ≤ n := hm.1.2.1
      by_contra hlt
      have hn : n = 1 := by omega
      exact hm.1.2.2.2 (by simp [hn])
  have hmod : IsRank2Model257 N.K n := ⟨hn2, hmodel⟩
  obtain ⟨K₁, K₂, V, V', s, c⟩ := N.conf257 h.borel h.nonIso h.p121 h.geom h.maxRank h.cover
    h.torus h.autOdd hlv hmod
  exact c.false_endgame hlv (h.nonIso ↥N.K n hn2 hmodel).2.2.2.2

end CFSG.QuasithinUnique
