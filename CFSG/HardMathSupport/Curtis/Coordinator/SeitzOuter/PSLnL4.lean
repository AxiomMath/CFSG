module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnAlt8
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnL28
public import CFSG.LargeExtraspecial.S4TwoH

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank

theorem l4TwoPlanes : L4TwoPlanes := by
  intro k _ _ hk p hp hp2
  have e₁ : Nonempty (alternatingGroup (Fin 8) ≃* StatedProj (StatedSL 4 (ZMod 2))) :=
    CFSG.LargeExtraspecial.S4.nonempty_mulEquiv_psl_of_alternating_eight (MulEquiv.refl _)
  obtain ⟨e₁⟩ := e₁
  have := Fintype.ofFinite k
  have hcard : Fintype.card (ZMod 2) = Fintype.card k := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hk]
  let e : alternatingGroup (Fin 8) ≃* projectiveSL 4 k :=
    ((e₁.trans (projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 2)).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 2))).trans
      (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard))
  exact (planeCentGen_alt8 hp hp2).of_mulEquiv e

theorem kFactSeitzOuterCubeRankTwoAtPrime_A_final
    {m : ℕ} (hm : 1 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} [Fact p.Prime]
    (hexc : ¬ (m = 2 ∧ p = 3 ∧ 3 ∣ q.card - 1)) :
    CFSG.AGLEmbedding.KFactSeitzOuterCubeRankTwoAtPrime ⟨.A m q, hv⟩ p :=
  kFactSeitzOuterCubeRankTwoAtPrime_A' l4TwoPlanes hm hv hexc

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
