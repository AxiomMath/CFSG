module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Blueprint

@[expose] def SzRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), BenderHyp G L → ∀ m : ℕ, 1 ≤ m →
    SuzukiModel (rankTwoQuot L) 2 (2 * m + 1) →
      m = 1 ∧ NativeSporadic.IsSporadic (rankTwoX L) .Ru

theorem sz_case_of_szRes (h : SzRes) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
      standardComponentOddCore G = ⊥ → ∀ m : ℕ, 1 ≤ m →
        SuzukiModel (rankTwoQuot A) 2 (2 * m + 1) →
          m = 1 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru :=
  fun G _ _ A hA hO m hm hs =>
    h G A ⟨hA.standard, hO, hA.not_normal, hA.rank, Or.inr (Or.inr ⟨m, hm, hs⟩)⟩ m hm hs

structure SzMinCounter (G : Type) [Group G] [Finite G] (L : Subgroup G) (m : ℕ) : Prop where
  hyp : BenderHyp G L
  one_le : 1 ≤ m
  sz : SuzukiModel (rankTwoQuot L) 2 (2 * m + 1)
  not_concl : ¬ (m = 1 ∧ NativeSporadic.IsSporadic (rankTwoX L) .Ru)
  ih : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → ∀ L' : Subgroup H,
    BenderHyp H L' → ∀ m' : ℕ, 1 ≤ m' → SuzukiModel (rankTwoQuot L') 2 (2 * m' + 1) →
      m' = 1 ∧ NativeSporadic.IsSporadic (rankTwoX L') .Ru

theorem szRes_of_szMinCounter
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (m : ℕ), SzMinCounter G L m → False) :
    SzRes := by
  suffices H : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ L : Subgroup G, BenderHyp G L → ∀ m : ℕ, 1 ≤ m →
        SuzukiModel (rankTwoQuot L) 2 (2 * m + 1) →
          m = 1 ∧ NativeSporadic.IsSporadic (rankTwoX L) .Ru by
    intro G _ _ L hL m hm hs
    exact H _ G rfl L hL m hm hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn L hL m hm hs
    by_contra hc
    exact h G L m ⟨hL, hm, hs, hc, fun H _ _ hH L' hL' m' hm' hs' =>
      ih _ (hn ▸ hH) H rfl L' hL' m' hm' hs'⟩

theorem suzukiModel_of_mulEquiv' {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {f : ℕ}
    (h : SuzukiModel Q' 2 f) : SuzukiModel Q 2 f := by
  obtain ⟨hp, a, ha, K, hK1, hK2, hf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK1, hK2, hf, hcard, ⟨e.trans e'⟩⟩

namespace SzMinCounter

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}

theorem nonempty_mulEquiv_sz (h : SzMinCounter G L m) : Nonempty (rankTwoQuot L ≃* Sz m) := by
  obtain ⟨a, -, hf, he⟩ := exists_mulEquiv_sz_of_suzukiModel h.sz
  have : a = m := by omega
  exact this ▸ he

end SzMinCounter

end CFSG.ComponentClassification.GMS78
