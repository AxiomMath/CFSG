module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def TwE6CentralizerConnOdd : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.E6 L Fr) →
    ¬ 3 ∣ S.D.q + 1 → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) → ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
        y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))

@[expose] def TwE6SmallExit : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    (hS : Setup p L J A d b),
    catalogIs (PSimple p L) (onLie fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2) →
    ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b →
    (catalogIs (PSimple p J) (ambiguousChev 2) ∨
      catalogIs (PSimple p J) (onLie fun i : TauCeti.LieTypeIndex =>
        (∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2) ∨ i = .tits) ∨
      Nat.card (PSimple p J) = 360) →
    (MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360) →
    InducesInnerMod p J b

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
