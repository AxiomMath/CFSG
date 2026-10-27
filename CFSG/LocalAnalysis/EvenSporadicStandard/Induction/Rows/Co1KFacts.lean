module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.Sporadic.Co1Block.TwoBD

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block


theorem card_quotient_twoBD : Nat.card (↥twoBD ⧸ center ↥twoBD) = 251596800 := by
  have := isSimpleGroup_twoBD
  rw [card_quotient_center_of_isSimpleGroup (by rw [card_twoBD]; norm_num), card_twoBD]

theorem co1_kNotExc (X : Type) [Group X] (hX : IsOddCentralExt ↥twoBD X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_oddCentralExt (c := 795) card_quotient_twoBD (by norm_num) (by norm_num)
    (by norm_num) X hX

theorem co1_pinned : Finite (Carrier .Co1) ∧ IsSimpleGroup (Carrier .Co1) ∧
    (∃ a b : Carrier .Co1, a * b ≠ b * a) ∧ Nat.card (Carrier .Co1) = 4157776806543360000 := by
  have h := CFSG.Sporadic.Co1.fam_co1_simplicity
  have hc : Nat.card (Carrier .Co1) = 4157776806543360000 := CFSG.Sporadic.Co1.card_Co1
  have : IsSimpleGroup (Carrier .Co1) := h.2.2
  exact ⟨h.1, h.2.2, nonabelian_of_isSimpleGroup_of_not_prime (by rw [hc]; norm_num), hc⟩

theorem co1_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Co1] X)
    (hY : IsOddCentralExt ↥twoBD (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 4157776806543360000) co1_pinned.1 co1_pinned.2.1
    co1_pinned.2.2.1 co1_pinned.2.2.2 (by decide) (by rw [card_quotient_twoBD]; norm_num) hX hY

end CFSG.EvenSporadicStandard.Induction
