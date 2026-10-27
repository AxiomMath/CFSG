module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Solomon.Coordinator


variable {G : Type} [Group G] [Finite G]

theorem i1131At_holds
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I1131At G p :=
  i1131At_of_tables tables112_holds tableL2_unconditional tables112Types_holds hsimple hKP hp hp2

end CFSG.LocalAnalysis.GLTheoremA
