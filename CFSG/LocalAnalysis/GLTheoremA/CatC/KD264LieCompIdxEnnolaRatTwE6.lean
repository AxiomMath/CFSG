module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatOuterD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie
namespace ExcUntw

section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

theorem ratCatExp_E6_all
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogueExp S i := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact ⟨_, Or.inl rfl,
      catalogueOver_rationalComponent_typeA S hp hT hap h1 i hA hq⟩
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact ratCatExp_of_inner_nonA_E6 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact ratCatExp_of_outerD_all S hp hT hap h1 i hD' hinner
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

end

end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section

open ExcUntw

theorem twistedE6RationalCatalogueExp_holds
       :
    TwistedE6RationalCatalogueExp := by
  intro L _ _ p₀ S _ p hp _ a hT hap h1 i hq
  exact ratCatExp_E6_all S hp hT hap h1 i hq

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
