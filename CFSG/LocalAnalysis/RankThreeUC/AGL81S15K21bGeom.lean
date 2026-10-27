module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bStmt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bTrans
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bOrd
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bEight
import CFSG.Quasithin.Vol2.Ch11SecBL2UKp
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bGeomProof

open K21bOrdProof K21bPtsProof

theorem geomAt_psl (F : Type) [Field F] [Finite F] [CharP F 2] :
    K21bGeomAt (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  obtain ⟨n, hn1, hq⟩ := card_eq_two_pow (F := F)
  by_cases h2 : Nat.card F = 2
  · intro E U hE hc hU hperm
    exfalso
    have hP : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 168 := by
      rw [CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA (K := F) (n := 3) (by norm_num), h2]
      decide
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rw [hc, hP] at hdvd
    omega
  by_cases h8 : Nat.card F = 8
  · intro E U hE hc hU hperm
    exact (K21bEightProof.no_elemAbelian_psl_eight F h8 E hE hc).elim
  have h4 : 4 ≤ Nat.card F := by
    rw [hq]
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      apply h2
      rw [hq, this]
      norm_num
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  refine K21bGeomAt.of_sylow isSylowOf_U0P ?_
  intro E hE hc hperm
  exact geom_psl_upper h4 h8 hc hperm

end K21bGeomProof

theorem K21bGeom_holds : K21bGeom := by
  intro S _ _ hS E U hE hc hU hperm
  suffices h : K21bGeomAt S from h E U hE hc hU hperm
  rcases hS with hL | ⟨d, Q, hQp, hd, ⟨e⟩⟩
  · intro E U hE hc hU hperm
    exfalso
    have h168 := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq hL
    have hdvd := Subgroup.card_subgroup_dvd_card E
    rw [hc, h168] at hdvd
    omega
  · obtain ⟨t, hv⟩ := d
    have ht : t = TauCeti.LieTypeIndex.A 2 Q := hd
    subst ht
    haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
    haveI : CharP (GaloisField Q.p Q.exponent) 2 := CharP.congr Q.p hQp
    exact K21bGeomAt.of_mulEquiv
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv))
      (K21bGeomProof.geomAt_psl (GaloisField Q.p Q.exponent))

end CFSG.LocalAnalysis.RankThreeUC.S15
