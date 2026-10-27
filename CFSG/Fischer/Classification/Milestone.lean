module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.OrderForm

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open Matrix

theorem milestone_of_statement
    (h : Statement)
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hsimple : IsSimpleGroup (commutator G)) :
    (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
    (∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) ∨
    (Nat.card G = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∧ Nat.card D = 3510) ∨
    (Nat.card G = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∧ Nat.card D = 31671) ∨
    (Nat.card G = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 ∧
      Nat.card D = 306936) := by
  have hP : Pair G D := ⟨inferInstance, hclass, hinv, hprod, hgen⟩
  rcases h G D ⟨hP, hcenter, hsimple⟩ with hc | ⟨k, hk⟩
  · rcases hc with h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    match k, hk with
    | ⟨0, _⟩, hk => exact Or.inl (CFSG.Fischer.card_of_hasType_F22 hP hcenter hsimple hk)
    | ⟨1, _⟩, hk =>
      exact Or.inr (Or.inl (CFSG.Fischer.card_of_hasType_F23 hP hcenter hsimple hk))
    | ⟨2, _⟩, hk =>
      exact Or.inr (Or.inr (CFSG.Fischer.card_of_hasType_F24 hP hcenter hsimple hk))

end CFSG.Fischer.Classification
