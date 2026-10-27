module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ConjCCard
public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Schreier

theorem card_centralizer_involution_GA
    {t : GA} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set GA)) = 89181388800 ∨
      Nat.card (Subgroup.centralizer ({t} : Set GA)) = 389283840 ∨
      Nat.card (Subgroup.centralizer ({t} : Set GA)) = 2012774400 := by
  rcases involution_classes.1 t ht with h | h | h
  · left
    rw [card_centralizer_eq_of_isConj h, card_centralizer_GA, coe_aC]
    exact card_cent_aG
  · right
    left
    rw [card_centralizer_eq_of_isConj h, card_centralizer_GA, coe_cC]
    exact card_cent_cG
  · right
    right
    rw [card_centralizer_eq_of_isConj h]
    exact card_cent_a₁

theorem card_centralizer_involution_of_isSporadic_co1
    {Y : Type} [Group Y] (hY : IsSporadic Y .Co1) {u : Y}
    (hu : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set Y)) = 89181388800 ∨
      Nat.card (Subgroup.centralizer ({u} : Set Y)) = 389283840 ∨
      Nat.card (Subgroup.centralizer ({u} : Set Y)) = 2012774400 := by
  obtain ⟨e⟩ := hY
  let f : Y ≃* GA := MulEquiv.trans (e : Y ≃* NativeSporadic.Co1) co1MatEquiv
  have h2 : orderOf (f u) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hu
  have h3 := @card_centralizer_equiv Y GA _ inferInstance f u
  rw [h3]
  exact card_centralizer_involution_GA h2

end CFSG.EvenSporadicStandard.TwoCo1
