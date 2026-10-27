module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThree
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

section GraphA

theorem noNormalCop_fixSub_graphType (hR : TrialityThreeRest) {K : Type} [Field K] [Finite K]
    (hK3 : ¬ 3 ∣ Nat.card K) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1) :
    NoNormalCop 3 (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have hKc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  haveI : Fact (ringChar K).Prime := ⟨hpr⟩
  have hℓ3 : ringChar K ≠ 3 := by
    intro h
    apply hK3
    rw [hKc, h]
    exact dvd_pow_self 3 n.pos.ne'
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφo, ⟨e⟩⟩ :=
    exists_dual_fixEquiv n.pos K hKc _ hα g a hε rfl
  have hcf := coreFreeAt_three_graphFixedRootGroup_D4 hR hpr hℓ3 n.pos hK₃ Fr hFr φ hφ3 hφo
  refine noNormalCop_of_mulEquiv e hcf.1

end GraphA

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
