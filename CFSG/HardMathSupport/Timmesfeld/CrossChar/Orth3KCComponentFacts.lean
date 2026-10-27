module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Local

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.quasisimple_specialBlock3 (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_quasisimple_specialBlock hx hp hp2 hK4 hh hne1 hm

theorem OddOrderIsometry.specialBlock_le_orthDerived3 (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) : specialBlock Q x h ≤ orthDerived Q :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_specialBlock_le_orthDerived hx hp hp2 hK4 hh
    hne1 hm

end CFSG.RankThree.PartOne.KCOrthogonal
