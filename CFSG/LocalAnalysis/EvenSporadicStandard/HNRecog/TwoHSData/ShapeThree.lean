module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ProdCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem isShapeCentralizerThree_of_data {G : Type} [Group G] [Finite G]
    (X L Y N V A : Subgroup G) (hLX : L ≤ X) (hYX : Y ≤ X) (hNY : N ≤ Y) (hVN : V ≤ N)
    (hAN : A ≤ N) (hX : Nat.card ↥X = Nat.card ↥L * Nat.card ↥Y)
    (hY : Nat.card ↥Y = 2 * Nat.card ↥N) (hN : Nat.card ↥N = Nat.card ↥V * Nat.card ↥A)
    (hLcen : ∀ l ∈ L, ∀ x ∈ X, x * l = l * x) (hLY : ∀ l ∈ L, l ∈ Y → l = 1)
    (hVcen : ∀ v ∈ V, ∀ n ∈ N, n * v = v * n) (hVA : ∀ v ∈ V, v ∈ A → v = 1)
    (hL : Nonempty (↥L ≃* Multiplicative (ZMod 3))) (hV : Nonempty (↥V ≃* Elem2 2))
    (hA : Nonempty (↥A ≃* alternatingGroup (Fin 5))) :
    IsShapeCentralizerThree ↥X := by
  let N' : Subgroup ↥Y := N.subgroupOf Y
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
  haveI : Nonempty ↥N := (OneMemClass.coe_nonempty N).to_subtype
  have hposN : 0 < Nat.card ↥N := Nat.card_pos
  have hidx : N'.index = 2 := by
    have h := Subgroup.index_mul_card (H := N')
    rw [hN'card, hY] at h
    exact Nat.mul_right_cancel hposN h
  haveI : N'.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨eN⟩ :=
    nonempty_mulEquiv_prod_of_central (X := N) (V := V) (S := A) hVN hAN hVcen hVA hN
  have hN'iso : Nonempty (↥N' ≃* Elem2 2 × alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hNY).trans
      (eN.trans (MulEquiv.prodCongr hV.some hA.some))⟩
  have hcard2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hquotcard : Nat.card (↥Y ⧸ N') = 2 := by
    have h := Subgroup.index_eq_card (H := N')
    rw [hidx] at h
    exact h.symm
  have hquotIso : Nonempty (↥Y ⧸ N' ≃* Multiplicative (ZMod 2)) :=
    ⟨mulEquivOfPrimeCardEq hquotcard hcard2⟩
  have hExt : IsExtensionShape ↥Y (Elem2 2 × alternatingGroup (Fin 5))
      (Multiplicative (ZMod 2)) :=
    ⟨N', inferInstance, hN'iso, hquotIso⟩
  obtain ⟨eX⟩ :=
    nonempty_mulEquiv_prod_of_central (X := X) (V := L) (S := Y) hLX hYX hLcen hLY hX
  have hXiso : Nonempty (↥X ≃* Multiplicative (ZMod 3) × ↥Y) :=
    ⟨eX.trans (MulEquiv.prodCongr hL.some (MulEquiv.refl ↥Y))⟩
  exact ⟨↥Y, inferInstance, hExt, hXiso⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
