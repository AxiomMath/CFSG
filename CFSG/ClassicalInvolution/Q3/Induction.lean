module

public import CFSG.ClassicalInvolution.Q3.LieSystem

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def CIT3Below (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → LieSystemMod3 Λ

@[expose] def CIT3Inductive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass3 Λ → LieSystemMod3 Λ

@[expose] def CIT3Step (n : ℕ) : Prop :=
  CIT3Below n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → LieSystemMod3 Λ

theorem cit3Inductive_of_step (h : ∀ n, CIT3Step n) : CIT3Inductive := by
  have key : ∀ n, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
      ∀ Λ : Set (Subgroup Y), InClass3 Λ → LieSystemMod3 Λ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y _ _ hY Λ hΛ
      exact h n (fun Y' _ _ hlt Λ' hΛ' => ih _ hlt Y' rfl Λ' hΛ') Y hY Λ hΛ
  intro Y _ _ Λ hΛ
  exact key _ Y rfl Λ hΛ

theorem CIT3Below.mono {m n : ℕ} (h : m ≤ n) (hn : CIT3Below n) : CIT3Below m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

@[expose] def LocalLieSystems3 {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ A : Set G, ¬ A ⊆ Subgroup.center G →
    LieSystemMod3 (restrictFamily (centralizingMembers Ω A) (centralizingLayer Ω A))

theorem localLieSystems3_of_cit3Below {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hBelow : CIT3Below (Nat.card G)) : LocalLieSystems3 Ω := by
  intro A hA
  by_cases hne : (centralizingMembers Ω A).Nonempty
  · exact hBelow _ (card_centralizingLayer_lt Ω hA) _ (inClass3_local hΩ A hne)
  · have hrf : restrictFamily (centralizingMembers Ω A) (centralizingLayer Ω A) = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨L, hL, _⟩ => hne ⟨L, hL⟩
    have hbot : centralizingLayer Ω A = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun L hL => (hne ⟨L, hL⟩).elim)
    have hsub : Subsingleton ↥(centralizingLayer Ω A) := by rw [hbot]; infer_instance
    have hq : Subsingleton (↥(centralizingLayer Ω A) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer Ω A)) := inferInstance
    exact LieSystem3.of_empty (by rw [hrf]; simp [oddQuotientFamily])

end CFSG.ClassicalInvolution.Q3
