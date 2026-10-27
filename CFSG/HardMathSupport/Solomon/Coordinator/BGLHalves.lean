module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26BGL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def BGLFieldPairGenerationU : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧ q % 3 ≠ 0 ∧ q ≠ 8 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSU 3 q F))) →
    ∀ b x : MulAut K,
      IsFieldAutThree b → b ≠ 1 → b ^ 3 = 1 → IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 →
        b * x = x * b →
          (⊤ : Subgroup K) ≤
            GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x))

theorem bglFieldPairGeneration_of_halves (hL : BGLFieldPairGenerationL)
    (hU : BGLFieldPairGenerationU) : BGLFieldPairGeneration := by
  intro K _ _ hK hT b x hb hb1 hb3 hx hx1 hx3 hbx
  rcases hT with hT | hT
  · exact hL K hK hT b x hb hb1 hb3 hx hx1 hx3 hbx
  · exact hU K hK hT b x hb hb1 hb3 hx hx1 hx3 hbx

theorem bglFieldPairGeneration_of_core (hcore : BGL.SL3SubfieldJoin)
    (hU : BGLFieldPairGenerationU) : BGLFieldPairGeneration :=
  bglFieldPairGeneration_of_halves (bglFieldPairGenerationL_of_core hcore) hU

end CFSG.HardMathSupport.Solomon.Coordinator
