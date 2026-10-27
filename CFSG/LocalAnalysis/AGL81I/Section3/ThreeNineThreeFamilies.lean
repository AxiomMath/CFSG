module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType IsSLType)
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)

@[expose] def ThreeNineThreeL34 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d →
    (StatedClassicalModel ↥K .PSL 3 2 2 ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧ IsSLType 3 F ↥K) → False

@[expose] def ThreeNineThreeA6Hat : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d → IsTripleCover ↥K (alternatingGroup (Fin 6)) → False

@[expose] def ThreeNineThreeL28 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d → StatedClassicalModel ↥K .PSL 2 2 3 → False

@[expose] def ThreeNineThreeD42 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d → ChevalleyExceptionalModel ↥K .trialityD4 2 1 → False

@[expose] def ThreeNineThreeChev : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d →
    (StatedClassicalModel ↥K .PSL 2 3 2 ∨ StatedClassicalModel ↥K .PSL 2 3 3 ∨
      IsPSLType 3 (ZMod 3) ↥K ∨ StatedClassicalModel ↥K .PSU 3 3 1 ∨
      StatedClassicalModel ↥K .PSp 2 3 1) → False

@[expose] def ThreeNineThreeAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d →
    (Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥K ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥K ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (↥K ≃* alternatingGroup (Fin 11))) → False

@[expose] def ThreeNineThreeSp62 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d → StatedClassicalModel ↥K .PSp 3 2 1 → False

@[expose] def ThreeNineThreeTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d → ReeTitsModel ↥K .Tits 2 1 → ThreeNineConclusion K D X₁ 3 d

@[expose] def ThreeNineThreeSpor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 3 d →
    (IsSporadic ↥K .M11 ∨ IsSporadic ↥K .M12 ∨ IsSporadic ↥K .J3) → False

@[expose] def ThreeNineThreeCoverRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    (IsTripleCover K McL ∨
      (∃ (Y : Type) (_ : Group Y), StatedClassicalModel Y .PSU 4 3 1 ∧ IsTripleCover K Y) ∨
      (∃ (Y : Type) (_ : Group Y), StatedClassicalModel Y .POmegaOdd 3 3 1 ∧
        IsTripleCover K Y) ∨
      (∃ (Y : Type) (_ : Group Y), ChevalleyExceptionalModel Y .G2 3 1 ∧ IsTripleCover K Y)) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)

@[expose] def ThreeNineThreeMcLRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSporadic K .McL → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)

theorem threeNineThreeMcLRank_holds : ThreeNineThreeMcLRank := by
  intro K _ _ hK
  obtain ⟨e'⟩ := hK
  dsimp only [CFSG.Blueprint.NativeSporadic.Carrier] at e'
  have : Finite CFSG.Blueprint.NativeSporadic.McL := Finite.of_equiv K e'.toEquiv
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
  have h1 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.McL) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc
  exact h1.trans_eq (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e').symm

theorem threeNineThree_of_members (hL34 : ThreeNineThreeL34) (hA6 : ThreeNineThreeA6Hat)
    (hL28 : ThreeNineThreeL28) (hD42 : ThreeNineThreeD42) (hChev : ThreeNineThreeChev)
    (hAlt : ThreeNineThreeAlt) (hSp : ThreeNineThreeSp62) (hTits : ThreeNineThreeTits)
    (hSpor : ThreeNineThreeSpor) (hCov : ThreeNineThreeCoverRank)
    (hMcL : ThreeNineThreeMcLRank)
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 3 d) (hK : KGroupLowRank24_12 3 ↥K) :
    ThreeNineConclusion K D X₁ 3 d := by
  have hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt (le_top : K ⊔ E ≤ ⊤)).trans h.rank_le
  have hrkK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := pRank_top_le_three_of_sup h.prime hrk
  obtain ⟨-, -, -, -, hK⟩ := hK
  rcases hK with (hK | hK | hK | hK | hK | hK | hK | hK | hK) | ⟨h3, -⟩ |
      ⟨-, hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK⟩ |
      ⟨h5, -⟩ | ⟨h7, -⟩ | ⟨h11, -⟩
  · exact (hAlt X K E D X₁ d h (Or.inl hK)).elim
  · exact (hAlt X K E D X₁ d h (Or.inr (Or.inl hK))).elim
  · exact (hChev X K E D X₁ d h (Or.inl hK)).elim
  · exact (hChev X K E D X₁ d h (Or.inr (Or.inl hK))).elim
  · exact (hChev X K E D X₁ d h (Or.inr (Or.inr (Or.inl hK)))).elim
  · exact (hChev X K E D X₁ d h (Or.inr (Or.inr (Or.inr (Or.inl hK))))).elim
  · exact absurd (four_le_pRank_of_isPSLType_four h.prime h.ne_two hK) (by omega)
  · exact absurd (four_le_pRank_of_psu_four h.ne_two hK) (by omega)
  · exact (hChev X K E D X₁ d h (Or.inr (Or.inr (Or.inr (Or.inr hK))))).elim
  · omega
  · exact (hL28 X K E D X₁ d h hK).elim
  · exact (hL34 X K E D X₁ d h (Or.inl hK)).elim
  · exact (hSp X K E D X₁ d h hK).elim
  · exact (hD42 X K E D X₁ d h hK).elim
  · exact hTits X K E D X₁ d h hK
  · exact (hAlt X K E D X₁ d h (Or.inr (Or.inr (Or.inl hK)))).elim
  · exact (hAlt X K E D X₁ d h (Or.inr (Or.inr (Or.inr hK)))).elim
  · exact (hSpor X K E D X₁ d h (Or.inl hK)).elim
  · exact (hSpor X K E D X₁ d h (Or.inr (Or.inl hK))).elim
  · exact (hSpor X K E D X₁ d h (Or.inr (Or.inr hK))).elim
  · exact absurd (hMcL ↥K hK) (by omega)
  · exact (hL34 X K E D X₁ d h (Or.inr hK)).elim
  · exact (hA6 X K E D X₁ d h hK).elim
  · exact absurd (hCov ↥K h.quasisimple (Or.inl hK)) (by omega)
  · exact absurd (hCov ↥K h.quasisimple (Or.inr (Or.inl hK))) (by omega)
  · exact absurd (hCov ↥K h.quasisimple (Or.inr (Or.inr (Or.inl hK)))) (by omega)
  · exact absurd (hCov ↥K h.quasisimple (Or.inr (Or.inr (Or.inr hK)))) (by omega)
  · omega
  · omega
  · omega

end CFSG.LocalAnalysis.AGL81I.Section3
