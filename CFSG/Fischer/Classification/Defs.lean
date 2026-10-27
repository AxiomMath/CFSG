module

public import CFSG.Blueprint.FischerDefs
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open Matrix

@[expose] def IsSymplecticType {X : Type} [Group X] (E : Set X) : Prop :=
  ∀ d ∈ E, ∀ e ∈ E, ∀ z ∈ E, d * e ≠ e * d →
    z * d = d * z ∨ z * e = e * z ∨ z * (d * e * d) = d * e * d * z

@[expose] def ClassicalConclusion (G : Type) [Group G] (D : Set G) : Prop :=
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
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1))

@[expose] def Conclusion (G : Type) [Group G] (D : Set G) : Prop :=
  ClassicalConclusion G D ∨ ∃ k : Fin 3, HasType k G D

end CFSG.Fischer.Classification
