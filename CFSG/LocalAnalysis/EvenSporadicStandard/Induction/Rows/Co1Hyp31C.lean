module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24Unique

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def Co1NotInG2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (N : Type) [Group N], LieModel N .G2 0 2 n → ∀ L : Subgroup N,
    ¬ IsSporadic ↥L .Co1

@[expose] def Co1CoverRank : Prop :=
  (∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .Co1 →
      Even (Nat.card (center X)) → 3 ≤ CFSG.pRank 2 X) ∧
    ∀ n : ℕ, 2 ≤ n → ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      LieModel (X ⧸ center X) .G2 0 2 n → 3 ≤ CFSG.pRank 2 X


theorem co1_fStar_cases {Y : Type} [Group Y] [Finite Y] (h412 : Sol78Thm412FSAt Y)
    {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P) {n : ℕ} (hn : 2 ≤ n)
    (hL : LieModel (↥P ⧸ center ↥P) .G2 0 2 n) :
    (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .G2 0 2 (2 * m)) ∨
      (LieModel ↥P .G2 0 2 2 ∧ IsSporadic ↥N' .Co1) :=
  h412 N' hN hidx hK P hP hPq ⟨n, hn, hL⟩

theorem co1R_lie {X : Type} [Group X] (hR : Co1R X) (hns : ¬ IsSporadic X .Co1) :
    ∃ n : ℕ, 2 ≤ n ∧ LieModel X .G2 0 2 n := by
  rcases hR with hs | h
  · exact absurd hs hns
  · exact h

theorem co1_closure (h412 : Sol78Thm412FSHered) :
    ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → ∀ (N' : Subgroup Y),
      FStarSimple N' → N'.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
      ∀ P : Subgroup Y, SolStd P →
        CFSG.IsQuasisimple ↥P → Co1R (↥P ⧸ center ↥P) →
        (¬ ∃ s ∈ [TauCeti.SporadicName.Co1] ++ [], IsSporadic (↥P ⧸ center ↥P) s) →
        (Odd (Nat.card ↥(center ↥P)) →
          ¬ ∃ s ∈ ([] : List TauCeti.SporadicName), IsSporadic (↥P ⧸ center ↥P) s) →
        (KEven IsKCo1O → ∀ (X : Type) [Group X], IsKCo1O X →
          Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
            HasEvenCover ↥N') → ClosureScope IsKCo1O N' P → Co1R ↥N' := by
  intro Y _ _ hUY N' hN hidx hK P hP hPq hR hns _ _ _
  obtain ⟨n, hn, hL⟩ := co1R_lie hR (fun hs => hns ⟨.Co1, by simp, hs⟩)
  rcases co1_fStar_cases (h412 Y hUY) hN hidx hK hP hPq hn hL with ⟨m, hm, hNm⟩ | ⟨-, hCo⟩
  · exact Or.inr ⟨2 * m, by omega, hNm⟩
  · exact Or.inl hCo

theorem co1_pair_into (h412 : Sol78Thm412FSHered) (g24 : LieModel ↥twoBD .G2 0 2 2) :
    ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → ∀ (N' : Subgroup Y),
      FStarSimple N' → N'.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
      ∀ P : Subgroup Y, SolStd P →
        CFSG.IsQuasisimple ↥P → Co1R (↥P ⧸ center ↥P) →
        (¬ ∃ s ∈ [TauCeti.SporadicName.Co1] ++ [], IsSporadic (↥P ⧸ center ↥P) s) →
        (Odd (Nat.card ↥(center ↥P)) →
          ¬ ∃ s ∈ ([] : List TauCeti.SporadicName), IsSporadic (↥P ⧸ center ↥P) s) →
        (KEven IsKCo1O → ∀ (X : Type) [Group X], IsKCo1O X →
          Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
            HasEvenCover ↥N') →
        (∃ s ∈ [TauCeti.SporadicName.Co1], IsSporadic ↥N' s) → IsKCo1O (↥P ⧸ CFSG.oddCore ↥P) := by
  intro Y _ _ hUY N' hN hidx hK P hP hPq hR hns _ _ ⟨s, hs, hsN⟩
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨n, hn, hL⟩ := co1R_lie hR (fun hs => hns ⟨.Co1, by simp, hs⟩)
  rcases co1_fStar_cases (h412 Y hUY) hN hidx hK hP hPq hn hL with ⟨m, hm, hNm⟩ | ⟨hP4, -⟩
  · exfalso
    have h1 : Nat.card ↥N' = 4157776806543360000 := co1_card_pinned _ hsN
    have h2 := card_of_lieModel_g_two (2 * m) hNm
    exact ordG2_ne_card_co1 (n := 2 * m) (by omega) (by rw [← h2, h1])
  · obtain ⟨e⟩ := lieModel_g24_equiv hP4 g24
    obtain ⟨-, -, -, -, hO⟩ := isKCo1O_facts ⟨e⟩
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩

theorem co1_notR (hmult : OddMultTrivial .Co1) (hno : Co1NotInG2) :
    ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
      (∃ L : Subgroup Y, InL L ∧ ∃ s ∈ [TauCeti.SporadicName.Co1], OddCover s L) →
        ¬ Co1R ↥N := by
  intro Y _ _ N hN hidx _ ⟨L, hL, s, hs, hcov⟩ hR
  rcases List.mem_singleton.1 hs with rfl
  have : N.Normal := hN.normal
  have hLN : L ≤ N := le_of_perfect_of_index_le_two hidx hcov.1.1
  have hne : L ≠ N := inL_ne_of_fStarSimple hN hL
  have hLsp : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
  rcases hR with hN1 | ⟨n, hn, hG2⟩
  · have h1 := co1_card_pinned _ hLsp
    have h2 := co1_card_pinned _ hN1
    have h3 : Nat.card ↥L ≤ Nat.card ↥N := Subgroup.card_le_of_le hLN
    exact hne (Subgroup.eq_of_le_of_card_ge hLN (by omega))
  · obtain ⟨e⟩ := hLsp
    exact hno n hn ↥N hG2 (L.subgroupOf N) ⟨(Subgroup.subgroupOfEquivOfLe hLN).trans e⟩

theorem co1_rank (hrk : Co1CoverRank) :
    ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Co1R (X ⧸ center X) →
      (Odd (Nat.card (center X)) →
        ¬ ∃ s ∈ [TauCeti.SporadicName.Co1] ++ [], IsSporadic (X ⧸ center X) s) →
      3 ≤ CFSG.pRank 2 X := by
  intro X _ _ hq hR hodd
  rcases hR with hs | ⟨n, hn, hX⟩
  · have hev : Even (Nat.card (center X)) := by
      by_contra h
      exact hodd (Nat.not_even_iff_odd.1 h) ⟨.Co1, by simp, hs⟩
    exact hrk.1 X hq hs hev
  · exact hrk.2 n hn X hq hX

end CFSG.EvenSporadicStandard.Induction
