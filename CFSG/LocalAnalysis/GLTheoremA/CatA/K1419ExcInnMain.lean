module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnTypeA
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDF4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE7
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

section Main


theorem char2L3U3_inner_of_big (hF : L3U3Facts) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hbig : InnerBigNonA τ) :
    Char2L3U3 τ .inner := by
  have hs : RDSize τ := by
    rcases hτ with rfl | rfl | rfl | rfl
    exacts [rdSize_F4, rdSize_E6, rdSize_E7, rdSize_E8]
  have hg : RDGlue τ := by
    rcases hτ with rfl | rfl | rfl | rfl
    exacts [rdGlue_F4, rdGlue_E6, rdGlue_E7, rdGlue_E8]
  intro L _ _ _ p₀ S a hT hap h1 i hk hq hL
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  rcases hs L a hap i with h2 | h6 | h14
  · exact (l3u3_inn_a1_false hF D (forall_eq_or_eq_neg_of_ncard_two hΨ h2) hL).elim
  · exact l3u3_inn_a2_central hF hT hap h1 D hg h6 hL
  · exfalso
    by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1)
    · exact l3u3_inn_typeA_false hF hT hap hk h14 hA hL
    · haveI := finite_rationalComponent S a i
      exact (hF.order _ hL).not_27_dvd (hbig L p₀ S a hT hap h1 i hk h14 hA hq)

end Main

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
