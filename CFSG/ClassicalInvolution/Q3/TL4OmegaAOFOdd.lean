module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.ClassicalInvolution.Q3.Q3MFOSOdd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance


theorem fixedOddFree_of_lieModel_pOmegaOdd {k : ℕ} {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : LieModel S .POmegaOdd k 3 1) : Q3NM.FixedOddFree S := by
  have hFT : IsFundTag StatedLieTag.POmegaOdd := trivial
  have hadm : StatedLieAdmissible .POmegaOdd k 3 1 :=
    (Upgrade.statedClassicalModel_of_lieModel (by decide) hS).1
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ k 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .POmegaOdd k 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .POmegaOdd k 3 1 Nat.prime_three hFT hadm).1).1⟩
  let e : S ≃* (modelUniv .POmegaOdd k 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .POmegaOdd k 3 1 Nat.prime_three).K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm
  exact Q3MFO.fixedOddFree_of_mulEquiv e (Q3MFO.fixedOddFree_pOmegaOdd hadm)

theorem outerFixedOddFree_pOmegaOdd {k : ℕ} : OuterFixedOddFree .POmegaOdd k :=
  fun _ _ _ _ hS σ hσ _ => fixedOddFree_of_lieModel_pOmegaOdd hS σ hσ

end CFSG.ClassicalInvolution.Q3.TL4
