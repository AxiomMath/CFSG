module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YFinal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

theorem abstract_A5WrTwo {X : Type} [Group X] [Finite X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {ρ : X →* (W ≃ₗ[ZMod 2] W)} {w : W} {P F : Subgroup X}
    {v : X} (h : WrData X ρ w P F v) (hsec : SmallSections X) : Nonempty (X ≃* A5WrTwo) := by
  let S : Subgroup X := CFSG.solvableRadical X
  have hfinal : FinalData (X ⧸ S) (P.map (QuotientGroup.mk' S))
      (F.map (QuotientGroup.mk' S)) (QuotientGroup.mk' S v) := finalData_quotient h
  have hsmall : SmallSections (X ⧸ S) := smallSections_quotient S hsec
  obtain ⟨e⟩ := final_A5WrTwo hfinal hsmall
  have hquot : Nat.card (X ⧸ S) = 7200 := by
    rw [Nat.card_congr e.toEquiv, natCard_A5WrTwo]
  have hX : Nat.card X = Nat.card (X ⧸ S) * Nat.card S :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup S
  have hle : Nat.card X ≤ 16200 := h.card_le
  rw [hX, hquot] at hle
  have hodd : Odd (Nat.card S) := (radical_structure h).2.2.2.2
  have hScard : Nat.card S = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hSbot : S = ⊥ := Subgroup.card_eq_one.1 hScard
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hSbot).trans
    QuotientGroup.quotientBot).symm.trans e⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
