module

public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {M : Type} [Field M]

theorem fixedFieldImage_index_dvd_card
    [Finite M] (σ : M ≃+* M) :
    (((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
      τ.cartan.det.natAbs ∧
      ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣
        (Nat.card (fixSubfield σ) - 1) ^ τ.rank) := by
  exact fixedFieldImage_index_dvd_and_card_units σ

end CFSG.LieType.Chevalley
