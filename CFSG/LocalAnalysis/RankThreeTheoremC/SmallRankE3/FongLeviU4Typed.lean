module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSL2Lie
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti

theorem u4_levi_pkg {A : Type} [Group A] [Finite A] {K₁ K₀ : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K₁ ≤ 1)
    (hpar : CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.IsParabolicTwo A K₁ K₀) (hne : K₀ ≠ K₁)
    {z : A} (hz : orderOf z = p) (hzK₀ : z ∈ K₀) {q : PrimePower} (hq2 : q.p = 2)
    (hm : 2 ≤ q.exponent) (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (e : ↥K₁ ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩)
    {q' : PrimePower} (hq'p : q'.p = 2) (hq'e : q'.exponent = 2 * q.exponent)
    (hv' : (LieTypeIndex.A 1 q').Valid) :
    LeviPkg p ⟨.A 1 q', hv'⟩ K₀ z := by
  have hmod : CFSG.Blueprint.LieModel ↥K₁ .PSU 4 2 q.exponent := by
    have h1 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hq2] at h1
    exact Or.inl ⟨by decide, h1⟩
  obtain ⟨K, _, h, ⟨e1⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hmod
  haveI := h.finite
  obtain ⟨-, hsec, hhom⟩ := u4_levi_of_equiv hp hp5 hKr hpar hne hz hzK₀ h hm e1.symm
  refine ⟨hsec, ?_⟩
  have hF : Nat.card K = q'.p ^ q'.exponent := by
    rw [h.card, hq'p, hq'e]
  obtain ⟨θ⟩ := nonempty_sl2_mulEquiv_lie (F := K) hq'p hv' hF
  exact hhom.of_mulEquiv θ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
