module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Defs


@[expose] def D4T2FixedSpinPerfect : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) → S.IsAlgebraic →
    ∀ {l f : ℕ}, l.Prime → 0 < f → S.D.q = l ^ f → l ≠ 3 → ((3 : ℕ) : L) ≠ 0 →
      3 ∣ l ^ f + 1 →
    ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit .E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard = 24 →
      twistInner (kernelRoots (rootCharHom a))
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) →
      ⁅rootSpan .E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model,
          rootSpan .E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model⁆ =
        rootSpan .E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model

end Defs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
