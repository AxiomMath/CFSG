module

import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TripleCoverKit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.Census219
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.Blueprint

theorem tp_eq_of_rep {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (h : Rep n T g) :
    tp n T = g := by
  have h1 : permOK n T = true :=
    CFSG.ComponentClassification.AS81.Q47.validA_of_rep (co2Rep_natArr_iff.2 h)
  exact rep_unique (rep_tp h1) h

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
