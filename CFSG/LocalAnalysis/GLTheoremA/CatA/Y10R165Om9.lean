module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om14
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmFam2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmFam3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus9
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ}

theorem concl165_of_torus (hT : OmTorusThree)
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1)
    {Ã : Subgroup ↥(orthDerived Q)} (hÃe : IsElemAbelian p Ã)
    (hÃmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(orthDerived Q)) ≤ CFSG.Open.pRank p Ã)
    (hÃ3 : 3 ≤ CFSG.Open.pRank p Ã)
    (hreg : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 2 ∧ ∃ ℓ : ℕ,
        Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        ℓ - 1 ≤ CFSG.Open.pRank p Ã)) :
    Concl165 ↥(orthDerived Q) p q Ã :=
  concl165_of_blocks hT hQ hn hp hp2 hq hq2 hqp hqdiv hÃe hÃmax hÃ3 hreg

theorem om165Engine_of_torus (hT : OmTorusThree) : Om165Engine := by
  intro F V _ _ _ _ _ _ Q hQ n p q hn hp hp2 hq hq2 hqp hqdiv Ã hÃe hÃmax hÃ3 hreg
  exact concl165_of_torus hT hQ hn hp hp2 hq hq2 hqp hqdiv hÃe hÃmax hÃ3 hreg

end OmEngine

section Certificate

theorem i165On_famTwD_of_torus (hT : OmTorusThree) : I165On i165FamTwD :=
  i165On_famTwD_of_engine (OmEngine.om165Engine_of_torus hT)

theorem i165On_famD_of_torus (hT : OmTorusThree) (hR : OmHypRankLower) : I165On i165FamD :=
  i165On_famD_of_engine (OmEngine.om165Engine_of_torus hT) hR

theorem i165On_famTwD_holds : I165On i165FamTwD :=
  i165On_famTwD_of_torus OmTorus.omTorusThree_holds

theorem i165On_famD_holds : I165On i165FamD :=
  i165On_famD_of_torus OmTorus.omTorusThree_holds OmTorus.omHypRankLower_holds

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
