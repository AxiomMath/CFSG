module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

@[expose] def SpPairedBlockModelDvd : Prop :=
  ∀ {m n p : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 2 ^ n → 2 ≤ m →
    p.Prime → p ≠ 2 →
    ∀ (x y : StatedSp m K), x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ≠ 1 →
    ∀ {h : K[X]}, (hh : h ∈ primaryFactors (spEnd x)) → h ≠ X - 1 →
      (h : K[X]) ≠ reciprocalPolynomial h →
      SpPairedBlock 2 n p x ⟨h, hh⟩ →
      ∀ J : Subgroup (StatedProj (StatedSp m K)),
        J = (⁅spSupported x ({h, reciprocalPolynomial h} : Set K[X]),
          spSupported x ({h, reciprocalPolynomial h} : Set K[X])⁆).map (proj m K) →
        (hN : proj m K y ∈ Subgroup.normalizer (J : Set (StatedProj (StatedSp m K)))) →
        p ∣ Nat.card J →
        Nonempty (LinBlockModel p J (proj m K y) hN) ∨
          MI.indAut p J (proj m K y) hN ∈ inner (PSimple p J)

theorem spPairedBlockModel_of_dvd (hmodel : SpPairedBlockModelDvd) : SpPairedBlockModel := by
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 h hh h1 hne hb J hJeq hN
  by_cases hpJ : p ∣ Nat.card J
  · exact hmodel hK hm hp hp2 x y hxp hyp hxy hx1 hh h1 hne hb J hJeq hN hpJ
  · haveI := subsingleton_pSimple_of_not_dvd hp hpJ
    exact Or.inr (mem_inner_of_subsingleton _)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
