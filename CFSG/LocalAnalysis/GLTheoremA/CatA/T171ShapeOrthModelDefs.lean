module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmCases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner)

abbrev OrthPairedBlockModel {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) : Prop :=
  ∀ {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
    (_hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
    (_hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
    (hyp : y ^ p = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
    (J : Subgroup (ProjOrthDerived Q))
    (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
    (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
    Nonempty (LinBlockModel p J (piOrth Q y) hN) ∨
      MI.indAut p J (piOrth Q y) hN ∈ inner (PSimple p J)

theorem orthPairedBlock_of_model {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hmodel : OrthPairedBlockModel Q) : OrthPairedBlock Q := by
  intro p hp hp2 x y hx hyc hyp h hh hne1 hne hq J hJeq hN
  rcases hmodel hp hp2 x y hx hyc hyp hh hne1 hne hq J hJeq hN with h | hI
  · obtain ⟨M⟩ := h
    exact Or.inl (linBlockModel_analysis hp hp2 M)
  · exact Or.inr hI

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
