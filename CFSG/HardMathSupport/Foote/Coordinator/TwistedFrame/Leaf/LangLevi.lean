module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.LangLeviAux
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


theorem exists_langLevi (τ : Tag) (K : Type) [Field K] [Finite K] (w : WeylGroup τ)
    (hw : w • highRoot τ = highRoot τ) : Nonempty (LangLevi τ K w) := by
  classical
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hcard' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hZ := LangLeviAux.isConnectedAlgebraicSubgroup_parabolicLevi (τ := τ)
    (k := AlgebraicClosure K) (Jθ τ)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ (e := (n : ℕ)) n.pos 1
    (fun g hg => LangLeviAux.frobTwistGL_one_mem_parabolicLevi p (n : ℕ) (Jθ τ) hg)
  have hn : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∈ Lθ τ (AlgebraicClosure K) :=
    canonicalRep_mem_parabolicLevi (mem_parabolicWeylGroup_of_smul_highRoot τ hw)
  obtain ⟨z, hz, hzn⟩ := hlang _ hn
  refine ⟨⟨AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) p n, fun c => ?_, z, hz, ?_⟩⟩
  · rw [iterateFrobenius_def, hcard']
  · have h1 : frobTwistGL τ (AlgebraicClosure K) p n 1 z =
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) p n)) z := by
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    rw [← hzn, mul_inv_cancel_left]
    exact h1.symm

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
