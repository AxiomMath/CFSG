module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

local instance finite_e6Group (F : Type) [Field F] [Finite F] :
    Finite ↥(Minuscule.e6Data_valid.minGroup F) :=
  CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup Minuscule.e6Data_valid F

local instance finite_e7Group (F : Type) [Field F] [Finite F] :
    Finite ↥(Minuscule.e7Data_valid.minGroup F) :=
  CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup Minuscule.e7Data_valid F

local instance finite_e8Group (F : Type) [Field F] [Finite F] :
    Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 F) :=
  CFSG.LieType.Chevalley.generated_group_finite .E8 F

theorem edgeCond_e6 (F : Type) [Field F] [Finite F] [CharP F 2]
    (H : Fin (Minuscule.e6Datum F).rank → Subgroup ↥(Minuscule.e6Data_valid.minGroup F))
    (hrank : 3 ≤ (Minuscule.e6Datum F).rank) (u v : Fin (Minuscule.e6Datum F).rank)
    (hadj : (TauCeti.diagramGraph (Minuscule.e6Datum F).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (Minuscule.e6Datum F) H u v := by
  obtain ⟨hne, hc⟩ := ((Minuscule.e6Datum F).isFiniteType.diagramGraph_adj_iff).1 hadj
  have h : adjE u.val v.val ∨ adjE v.val u.val := by
    by_contra hn
    exact hc ((cartan_E6_iff u v hne).2 hn)
  have h' : edgeE (Minuscule.e6Datum F).rank u v ∨ edgeE (Minuscule.e6Datum F).rank v u := h
  refine Or.inl ?_
  rcases h' with h' | h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
      (simplyLacedLevis_e6 F) h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_symm
      (CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
        (simplyLacedLevis_e6 F) h')

theorem edgeCond_e7 (F : Type) [Field F] [Finite F] [CharP F 2]
    (H : Fin (Minuscule.e7Datum F).rank → Subgroup ↥(Minuscule.e7Data_valid.minGroup F))
    (hrank : 3 ≤ (Minuscule.e7Datum F).rank) (u v : Fin (Minuscule.e7Datum F).rank)
    (hadj : (TauCeti.diagramGraph (Minuscule.e7Datum F).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (Minuscule.e7Datum F) H u v := by
  obtain ⟨hne, hc⟩ := ((Minuscule.e7Datum F).isFiniteType.diagramGraph_adj_iff).1 hadj
  have h : adjE u.val v.val ∨ adjE v.val u.val := by
    by_contra hn
    exact hc ((cartan_E7_iff u v hne).2 hn)
  have h' : edgeE (Minuscule.e7Datum F).rank u v ∨ edgeE (Minuscule.e7Datum F).rank v u := h
  refine Or.inl ?_
  rcases h' with h' | h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
      (simplyLacedLevis_e7 F) h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_symm
      (CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
        (simplyLacedLevis_e7 F) h')

theorem edgeCond_e8 (F : Type) [Field F] [Finite F] [CharP F 2]
    (H : Fin (Adjoint.e8Datum F).rank →
      Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 F))
    (hrank : 3 ≤ (Adjoint.e8Datum F).rank) (u v : Fin (Adjoint.e8Datum F).rank)
    (hadj : (TauCeti.diagramGraph (Adjoint.e8Datum F).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (Adjoint.e8Datum F) H u v := by
  obtain ⟨hne, hc⟩ := ((Adjoint.e8Datum F).isFiniteType.diagramGraph_adj_iff).1 hadj
  have h : adjE u.val v.val ∨ adjE v.val u.val := by
    by_contra hn
    exact hc ((cartan_E8_iff u v hne).2 hn)
  have h' : edgeE (Adjoint.e8Datum F).rank u v ∨ edgeE (Adjoint.e8Datum F).rank v u := h
  refine Or.inl ?_
  rcases h' with h' | h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
      (simplyLacedLevis_e8 F) h'
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_symm
      (CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis
        (simplyLacedLevis_e8 F) h')

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
