module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6P

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GH74Small (G : Type) [Group G] : Prop :=
  Blueprint.LieModel G .PSL 2 2 3 ∨ Blueprint.LieModel G .PSL 2 2 4 ∨
    Blueprint.LieModel G .PSL 3 2 2 ∨ Blueprint.LieModel G .twistedB2 0 2 3

@[expose] def GH74Alt (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def GH74Sp4 (G : Type) [Group G] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel G .PSp 2 p f

@[expose] def GH74L4U4 (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ Blueprint.LieModel G .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ Blueprint.LieModel G .PSU 4 p f)

@[expose] def GH74Exc (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel G .G2 0 p f ∨ Blueprint.LieModel G .trialityD4 0 p f)) ∨
    (∃ f : ℕ, Blueprint.LieModel G .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ Blueprint.LieModel G .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ Blueprint.LieModel G .PSU 5 p f)

@[expose] def GH74Spor (G : Type) [Group G] : Prop :=
  Blueprint.NativeSporadic.IsSporadic G .M12 ∨ Blueprint.NativeSporadic.IsSporadic G .M22 ∨
    Blueprint.NativeSporadic.IsSporadic G .M23 ∨ Blueprint.NativeSporadic.IsSporadic G .J1 ∨
    Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .J3 ∨
    Blueprint.NativeSporadic.IsSporadic G .McL ∨ Blueprint.NativeSporadic.IsSporadic G .Ly

theorem gh74List_cases {G : Type} [Group G] (h : GH74List G) :
    GH74Small G ∨ GH74Alt G ∨ GH74Sp4 G ∨ GH74L4U4 G ∨ GH74Exc G ∨ GH74Spor G := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h)))))))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

@[expose] def CF81E6P211Small : Prop := P211For GH74Small

@[expose] def CF81E6P211Alt : Prop := P211For GH74Alt

@[expose] def CF81E6P211Sp4 : Prop := P211For GH74Sp4

@[expose] def CF81E6P211L4U4 : Prop := P211For GH74L4U4

@[expose] def CF81E6P211Exc : Prop := P211For GH74Exc

@[expose] def CF81E6P211Spor : Prop := P211For GH74Spor

theorem p211For_of_or {C C₁ C₂ : ∀ (G : Type) [Group G], Prop}
    (hC : ∀ (G : Type) [Group G], C G → C₁ G ∨ C₂ G) (h₁ : P211For C₁) (h₂ : P211For C₂) :
    P211For C := by
  intro X _ _ hsimp hcent hX
  rcases hC _ hX with h | h
  · exact h₁ X hsimp hcent h
  · exact h₂ X hsimp hcent h

theorem cf81E6P211_of (hSm : CF81E6P211Small) (hAl : CF81E6P211Alt) (hSp : CF81E6P211Sp4)
    (hL : CF81E6P211L4U4) (hE : CF81E6P211Exc) (hSo : CF81E6P211Spor) : CF81E6P211 :=
  p211For_of_or (C₁ := GH74Small) (fun _ _ h => gh74List_cases h) hSm <|
    p211For_of_or (fun _ _ h => h) hAl <| p211For_of_or (fun _ _ h => h) hSp <|
      p211For_of_or (fun _ _ h => h) hL <| p211For_of_or (fun _ _ h => h) hE hSo

end CFSG.ComponentClassification.GSThmB
