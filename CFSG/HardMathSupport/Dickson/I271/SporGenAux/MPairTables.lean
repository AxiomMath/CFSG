module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.ComponentClassification.OuterAutomorphisms

theorem sporPair_M_of_centGen {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnot : ¬ SporadicOnePair .M p)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hBM : SporadicBMData)
    (hOne : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nat.card (Outer S) = 1)
    (hCG : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → CentGen p S) : SporPair .M p := by
  refine sporPair_of_centGen hSpM hp5 ?_
  intro S _ _ hsimple hnab ⟨e⟩
  haveI := hsimple
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have eC : S ≃* NativeSporadic.Carrier .M := e.trans (hBr .M).some.symm
  have hone : Nat.card (Outer S) = 1 := hOne S ⟨eC⟩
  have hout : Nat.card (Outer S) ≤ 2 := by rw [hone]; norm_num
  exact ⟨autRankLe2_of_offPair hp (by omega) hnot (offPair_M hBM.2.1 hBM.2.2) eC hcen hout, hout,
    hCG S ⟨eC⟩⟩

end CFSG.HardMathSupport.Dickson.I271
