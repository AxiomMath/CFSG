module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.ONSchreier

section Suz


theorem card_quotient_suzD : Nat.card (↥suzD ⧸ center ↥suzD) = 20160 := by
  have := suzD_simple
  rw [card_quotient_center_of_isSimpleGroup (by rw [card_suzD]; norm_num), card_suzD]

theorem suz_kNotExc (X : Type) [Group X] (hX : IsOddCentralExt ↥suzD X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_oddCentralExt (c := 34) card_quotient_suzD (by norm_num) (by norm_num)
    (by norm_num) X hX

theorem suz_pinned : Finite (Carrier .Suz) ∧ IsSimpleGroup (Carrier .Suz) ∧
    (∃ a b : Carrier .Suz, a * b ≠ b * a) ∧ Nat.card (Carrier .Suz) = 448345497600 :=
  ⟨(suz_simple_data (Y := Carrier .Suz) ⟨MulEquiv.refl _⟩).1,
    (suz_simple_data (Y := Carrier .Suz) ⟨MulEquiv.refl _⟩).2.1,
    (suz_simple_data (Y := Carrier .Suz) ⟨MulEquiv.refl _⟩).2.2, CFSG.Sporadic.Suz.card_Suz⟩

theorem suz_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Suz] X)
    (hY : IsOddCentralExt ↥suzD (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 448345497600) suz_pinned.1 suz_pinned.2.1 suz_pinned.2.2.1
    suz_pinned.2.2.2 (by decide) (by rw [card_quotient_suzD]; norm_num) hX hY

end Suz

section ON


theorem card_center_onL : Nat.card (center ↥onL) = 4 := by
  rw [← Subgroup.card_map_of_injective onL.subtype_injective,
    ← CFSG.centerIn_eq_map_center, onL_centerIn, card_onQ]

theorem card_quotient_onL : Nat.card (↥onL ⧸ center ↥onL) = 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥onL)
  rw [card_onL, card_center_onL] at h
  omega

theorem on_kNotExc (X : Type) [Group X] (hX : IsOddCentralExt ↥onL X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_oddCentralExt (c := 34) card_quotient_onL (by norm_num) (by norm_num)
    (by norm_num) X hX

theorem on_pinned : Finite (Carrier .ONan) ∧ IsSimpleGroup (Carrier .ONan) ∧
    (∃ a b : Carrier .ONan, a * b ≠ b * a) ∧ Nat.card (Carrier .ONan) = 460815505920 :=
  ⟨(on_simple_data (Y := Carrier .ONan) ⟨MulEquiv.refl _⟩).1,
    (on_simple_data (Y := Carrier .ONan) ⟨MulEquiv.refl _⟩).2.1,
    (on_simple_data (Y := Carrier .ONan) ⟨MulEquiv.refl _⟩).2.2, CFSG.Sporadic.ON.card_ON⟩

theorem on_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.ONan] X)
    (hY : IsOddCentralExt ↥onL (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 460815505920) on_pinned.1 on_pinned.2.1 on_pinned.2.2.1
    on_pinned.2.2.2 (by decide) (by rw [card_quotient_onL]; norm_num) hX hY

end ON

end CFSG.EvenSporadicStandard.Induction
