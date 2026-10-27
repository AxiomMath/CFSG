module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankLin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer
public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFRRank

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem card_gfTwo :
    haveI : Fact gfTwoPP.p.Prime := ⟨gfTwoPP.prime_p⟩
    Nat.card (GaloisField gfTwoPP.p gfTwoPP.exponent) = 2 := by
  haveI : Fact gfTwoPP.p.Prime := ⟨gfTwoPP.prime_p⟩
  rw [GaloisField.card _ _ gfTwoPP.exponent_pos.ne']
  rfl

theorem innerThree_catA (n : ℕ) (hn : 2 ≤ n) (hv : (TauCeti.LieTypeIndex.A n gfTwoPP).Valid) :
    InnerThree (TauCeti.ValidLieTypeIndex.Group ⟨.A n gfTwoPP, hv⟩) := by
  haveI : Fact gfTwoPP.p.Prime := ⟨gfTwoPP.prime_p⟩
  refine innerThree_of_mulEquiv
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n gfTwoPP hv).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) _).symm)) ?_
  intro β hβ
  exact CFSG.RankThree.PartTwo.Sec21.Hering214.inner_of_pow_three_eq_one card_gfTwo (by omega) hβ

theorem coreThree_catA (n : ℕ) (hn : 7 ≤ n) (hv : (TauCeti.LieTypeIndex.A n gfTwoPP).Valid) :
    CoreThree (TauCeti.ValidLieTypeIndex.Group ⟨.A n gfTwoPP, hv⟩) := by
  haveI : Fact gfTwoPP.p.Prime := ⟨gfTwoPP.prime_p⟩
  obtain ⟨σ⟩ := KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2 _ card_gfTwo
  refine coreThree_of_mulEquiv
    (((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n gfTwoPP hv).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) _).symm)).trans
        (KD264Lie.X1LinCore.Transfer.projEquiv (n + 1) σ)) ?_
  intro y hy
  exact exists_elemAb81_commute (by rw [Module.finrank_fin_fun]; omega) y hy

end CFSG.LocalAnalysis.GLTheoremA.SFRRank

end
