module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open CFSG.Open

@[expose] def GoldschmidtTheoremA : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K)

end CFSG.EvenSporadicStandard.HNRecog.Harada
