module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

theorem finite_spinGroup_plus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) :
    Finite (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F)) := by
  haveI : NeZero n := ⟨by omega⟩
  exact CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
    CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus

theorem edgeCond_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (H : Fin (CFSG.LieType.Universal.Spin.plusDatum n F hn).rank →
      Subgroup (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F)))
    (hrank : 3 ≤ (CFSG.LieType.Universal.Spin.plusDatum n F hn).rank)
    (u v : Fin (CFSG.LieType.Universal.Spin.plusDatum n F hn).rank)
    (hadj : (TauCeti.diagramGraph (CFSG.LieType.Universal.Spin.plusDatum n F hn).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond
      (CFSG.LieType.Universal.Spin.plusDatum n F hn) H u v := by
  haveI : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F)) :=
    finite_spinGroup_plus hn
  obtain ⟨hne, hc⟩ :=
    ((CFSG.LieType.Universal.Spin.plusDatum n F hn).isFiniteType.diagramGraph_adj_iff).1 hadj
  have hedge : CFSG.Timmesfeld.edgeD n u v ∨ CFSG.Timmesfeld.edgeD n v u := by
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.1 h
    exact hc (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD hne h1 h2).1
  refine Or.inl ?_
  rcases hedge with h | h
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
      (CFSG.Timmesfeld.simplyLacedLevis_spinPlus F hn) h
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_symm
      (CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
        (CFSG.Timmesfeld.simplyLacedLevis_spinPlus F hn) h)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
