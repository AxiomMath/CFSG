module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint TwE6UniqAbs

namespace TwE6InnerAbs

set_option maxRecDepth 100000

@[expose] def sD4 : Finset (Option (Fin Tag.E6.rank)) :=
  ({some 1, some 2, some 3, some 4} : Finset (Option (Fin 6)))

@[expose] def sA5a : Finset (Option (Fin Tag.E6.rank)) :=
  ({some 0, some 2, some 3, some 4, some 5} : Finset (Option (Fin 6)))

@[expose] def sA5b : Finset (Option (Fin Tag.E6.rank)) :=
  ({none, some 1, some 3, some 4, some 5} : Finset (Option (Fin 6)))

@[expose] def sA5c : Finset (Option (Fin Tag.E6.rank)) :=
  ({none, some 0, some 1, some 2, some 3} : Finset (Option (Fin 6)))

@[expose] def kcInnerB (zl : List ℕ) : Bool :=
  zl.all fun x => (szF zl x == 6) ||
    ((szF zl x == 24) && (cmpF zl x == sD4)) ||
      ((szF zl x == 30) && ((cmpF zl x == sA5a) || (cmpF zl x == sA5b) || (cmpF zl x == sA5c)))

set_option synthInstance.maxSize 1024 in
theorem kc_innerTypes : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (4 * m0.val + 3 * m1.val + 5 * m2.val + 6 * m3.val + 4 * m4.val + 2 * m5.val) % 3 = 0 →
    (m0.val % 3 ≠ 0 ∨ m1.val % 3 ≠ 0 ∨ m2.val % 3 ≠ 0 ∨ m3.val % 3 ≠ 0 ∨ m4.val % 3 ≠ 0 ∨
      m5.val % 3 ≠ 0) →
    kcInnerB (zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
