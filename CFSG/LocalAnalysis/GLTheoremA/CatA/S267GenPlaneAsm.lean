module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenQuasi
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem not_isD2SeitzException_of_core {p : ℕ} {d : TauCeti.LieTypeIndex}
    (hd : S2019.S2019ExcCoreIdx d) : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d := by
  rintro (⟨-, ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl | rfl⟩ | rfl⟩ |
    ⟨-, rfl | rfl⟩) <;> exact hd

section Assembly


theorem genPlaneExcAssembly_holds :
    GenNormalExcInner → GenNormalExcOuter → GenPlaneE6Three →
      GenPlaneCompOn S2019.S2019ExcCoreIdx := by
  intro hIn hOut hE6 p T _ _ d h hd P hP hcard J hJ
  by_cases hpe : p = 3 ∧ IsE6Eps d.1
  · obtain ⟨rfl, hE⟩ := hpe
    exact hE6 T d h hE P hP hcard J hJ
  obtain ⟨e⟩ := h.iso
  have hnorm : ∀ x ∈ P, x ≠ 1 → fixSubgroup x ≤ Subgroup.normalizer (J : Set T) := by
    intro x hx hx1
    have hxp : x ^ p = 1 := hP.2 x hx
    have hcomp := genCompQuasiOn_holds' S2019.S2019ExcCoreIdx p T d h hd x hxp hx1 J
      (hJ x hx hx1)
    by_cases hxi : x ∈ innAutDerived T
    · exact hIn p T d h hd hpe x hxp hx1 hxi J hcomp
    · exact hOut p T d h hd x hxp hx1 hxi J hcomp
  have hS := CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds d p h.prime h.odd h.ne
    (not_isD2SeitzException_of_core hd) (SL3CoverGen.mapAut e P)
    (hP.map (MulAut.congr e).toMonoidHom) ((SL3CoverGen.card_mapAut P e).trans hcard)
  have hgen : Subgroup.closure (SL3CoverGen.fixSet P) = ⊤ :=
    (SL3CoverGen.closure_fixSet_mapAut_eq_top_iff e P).mp hS
  have hN : Subgroup.normalizer (J : Set T) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro t ⟨x, hx, hx1, hxt⟩
    exact hnorm x hx hx1 hxt
  haveI : J.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).2
  haveI : IsSimpleGroup T := e.isSimpleGroup
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    rcases P.bot_or_exists_ne_one with hbot | hne
    · have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
      have h2 := h.prime.two_le
      rw [hcard] at h1
      nlinarith
    · exact hne
  have hJx := hJ x hx hx1
  rcases Subgroup.Normal.eq_bot_or_eq_top J with hbot | htop
  · exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJx hbot
  have hcomp := genCompQuasiOn_holds' S2019.S2019ExcCoreIdx p T d h hd x (hP.2 x hx) hx1 J hJx
  apply hx1
  ext t
  have ht : t ∈ fixSubgroup x := hcomp.1 (htop ▸ Subgroup.mem_top t)
  rw [MulAut.one_apply]
  exact ht

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
