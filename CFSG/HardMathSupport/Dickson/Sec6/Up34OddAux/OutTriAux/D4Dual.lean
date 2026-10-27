module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.Odd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Dual


theorem noL34Layer_of_graphType (hA2 : TriD4A2NoL34) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) : NoL34Layer α := by
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    exists_dual_fixEquiv hf K hK α hα3 g a hε hαeq
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 Fr
  exact noL34Layer_of_fixEquiv e
    (noL34Layer_three_D4_outer_odd hA2 Fact.out hℓ5 hf hK₃ Fr hFr φ hφ3 hφout)

end Dual

end CFSG.HardMathSupport.Dickson.Sec6.OutTri
