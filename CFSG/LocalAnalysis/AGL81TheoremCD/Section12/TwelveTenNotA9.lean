module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def A9ThreeCycleStep (M H : Subgroup G) (L₁ L₂ L₃ : Subgroup G) (p : ℕ) : Prop :=
  Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)) →
    ∃ P W : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) ∧
      W ≤ kSub p M H ∧ (W ≤ L₁ ∨ W ≤ L₂ ∨ W ≤ L₃) ∧ Nat.card W = 3 ∧
      ¬ (Subgroup.centralizer (W : Set G) ⊓ kSub p M H) ≤
        (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H)

theorem not_nonempty_modTwoCore_equiv_alternatingGroup_nine
    {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h126 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (hstep : A9ThreeCycleStep M H L₁ L₂ L₃ p) :
    ¬ Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)) := by
  intro hA9
  obtain ⟨P, W, hP, hWK, hWL, hW3, hKW⟩ := hstep hA9
  have hcent : Subgroup.centralizer (W : Set G) ≤ M := by
    rcases hWL with h | h | h
    · exact TwelveSix.part_one_left hdata h126 W hW3 h
    · exact TwelveSix.part_one_middle hdata h126 W hW3 h
    · exact TwelveSix.part_one_right hdata h126 W hW3 h
  have hle : Subgroup.centralizer (W : Set G) ⊓ kSub p M H ≤ kSub p M H ⊓ M := by
    calc Subgroup.centralizer (W : Set G) ⊓ kSub p M H
        = kSub p M H ⊓ Subgroup.centralizer (W : Set G) := inf_comm _ _
      _ ≤ kSub p M H ⊓ M := inf_le_inf_left _ hcent
  have hEq : kSub p M H ⊓ M =
      (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H) :=
    h126.part_six hdata P hP
  exact hKW (hEq ▸ hle)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
