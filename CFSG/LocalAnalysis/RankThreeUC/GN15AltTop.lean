module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNInputRed

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def AltOddCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T),
      GNYComponent T T₁ T₂ Ls → ∀ n : ℕ, 8 < n → Odd n →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) → False

theorem altEven_of_altOddCover (h : AltOddCover) : GNInputRed.AltEven := by
  intro X _ _ T hX hT T₁ T₂ hC Ls hY n hn he
  by_contra hne
  exact h X T hX hT T₁ T₂ hC Ls hY n hn (Nat.not_even_iff_odd.mp hne) he

@[expose] def AltOddCoverPow : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T),
      GNYComponent T T₁ T₂ Ls → ∀ m : ℕ, 3 ≤ m →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin (2 ^ m + 1))) → False

@[expose] def AltOddCoverRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T),
      GNYComponent T T₁ T₂ Ls → ∀ n : ℕ, 8 < n → Odd n → (¬ ∃ m : ℕ, n = 2 ^ m + 1) →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) → False

theorem altOddCover_of_split (h1 : AltOddCoverPow) (h2 : AltOddCoverRest) : AltOddCover := by
  intro X _ _ T hX hT T₁ T₂ hC Ls hY n hn hodd he
  by_cases hm : ∃ m : ℕ, n = 2 ^ m + 1
  · obtain ⟨m, rfl⟩ := hm
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact h1 X T hX hT T₁ T₂ hC Ls hY m hm3 he
  · exact h2 X T hX hT T₁ T₂ hC Ls hY n hn hodd hm he

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
