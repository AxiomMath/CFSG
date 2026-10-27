module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FamilyArith
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1RowAtlas

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def Co1R : GroupClass := fun X _ =>
  IsSporadic X .Co1 ∨ ∃ n : ℕ, 2 ≤ n ∧ LieModel X .G2 0 2 n

theorem co1R_iso : GroupClass.IsoInv Co1R := by
  intro X Y _ _ e h
  rcases h with hX | ⟨n, hn, hX⟩
  · obtain ⟨f⟩ := hX
    exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨n, hn, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hX⟩


theorem card_of_lieModel_g_two (n : ℕ) {X : Type} [Group X] (h : LieModel X .G2 0 2 n) :
    Nat.card X = CFSG.Open.ordG2 (2 ^ n) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem isKCo1O_facts {X : Type} [Group X] (hX : IsKCo1O X) :
    Finite X ∧ IsSimpleGroup X ∧ Nat.card X = 251596800 ∧ center X = ⊥ ∧ CFSG.oddCore X = ⊥ := by
  obtain ⟨e⟩ := hX
  have hfin : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hs : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_twoBD e
  have hc : Nat.card X = 251596800 := by rw [Nat.card_congr e.toEquiv]; exact card_twoBD
  have hnc : ∃ a b : X, a * b ≠ b * a :=
    nonabelian_of_isSimpleGroup_of_not_prime (by rw [hc]; norm_num)
  have hZ : center X = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hnc
  refine ⟨hfin, hs, hc, hZ, ?_⟩
  have := hfin
  exact le_bot_iff.1 ((oddCore_le_center
    (isOddCentralExt_of_isKCo1O ⟨e⟩).1).trans hZ.le)

theorem co1_K_quot {X : Type} [Group X] (hX : IsKCo1O X) : IsKCo1O (X ⧸ CFSG.oddCore X) := by
  obtain ⟨e⟩ := hX
  obtain ⟨-, -, -, -, hO⟩ := isKCo1O_facts ⟨e⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩

theorem co1_K_iso {X Y : Type} [Group X] [Group Y] (hX : IsKCo1O X) (hY : IsKCo1O Y) :
    Nonempty (X ≃* Y) := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ := hY
  exact ⟨e.trans f.symm⟩

theorem co1_K_cq {X Y : Type} [Group X] [Group Y] (hX : IsKCo1O X) (hY : IsKCo1O Y) :
    Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  obtain ⟨-, -, -, hZX, -⟩ := isKCo1O_facts hX
  obtain ⟨-, -, -, hZY, -⟩ := isKCo1O_facts hY
  obtain ⟨e⟩ := co1_K_iso hX hY
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).symm)⟩

theorem co1_K_not_sporadic : ∀ (X : Type) [Group X], IsKCo1O X →
    ∀ s ∈ [TauCeti.SporadicName.Co1] ++ [], ¬ IsSporadic (X ⧸ center X) s := by
  intro X _ hX s hs
  rcases List.mem_singleton.1 (by simpa using hs) with rfl
  obtain ⟨hfin, -, hc, hZ, -⟩ := isKCo1O_facts hX
  intro h
  have h1 := co1_card_pinned _ h
  have h2 : Nat.card (X ⧸ center X) = 251596800 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, hc]
  omega

theorem co1_K_reach (g24 : LieModel ↥twoBD .G2 0 2 2) {X : Type} [Group X] (hX : IsKCo1O X) :
    Co1R (X ⧸ center X) := by
  obtain ⟨e⟩ := hX
  obtain ⟨-, -, -, hZ, -⟩ := isKCo1O_facts ⟨e⟩
  have f : (X ⧸ center X) ≃* ↥twoBD :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  exact Or.inr ⟨2, le_rfl, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv f.symm g24⟩

theorem co1_not_exc : ∀ (X : Type) [Group X], Co1R X → NotExc X := by
  intro X _ h
  rcases h with hX | ⟨n, hn, hX⟩
  · obtain ⟨e⟩ := hX
    exact notExc_of_card_group (N := 4157776806543360000) (c := 2025957)
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Co1.card_Co1) (by norm_num)
      (by norm_num) (by norm_num)
  · exact notExc_of_card_g2 (by omega) (card_of_lieModel_g_two n hX)

end CFSG.EvenSporadicStandard.Induction
