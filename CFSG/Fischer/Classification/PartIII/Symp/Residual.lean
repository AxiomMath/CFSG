module

public import CFSG.Fischer.Classification.PartIII.Symp.Kill

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Matrix

@[expose] def LocalSympCases (H : Type) [Group H] (F : Set H) : Prop :=
  (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
    ∃ φ : H ≃* Equiv.Perm (Fin m), ∀ g : H, g ∈ F ↔ (φ g).IsSwap) ∨
  (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
    fischerLinearModel F
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
  (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
    (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
    fischerLinearModel F
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))

@[expose] def SympResidual (H : Type) [Group H] (F : Set H) : Prop :=
  (∃ φ : H ≃* Equiv.Perm (Fin 5), ∀ g : H, g ∈ F ↔ (φ g).IsSwap) ∨
  (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
    (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
    2 ^ (2 * m - 1) < {v | Q v = 1}.ncard ∧
    fischerLinearModel F
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))

variable {G : Type} [Group G] {D : Set G}

theorem false_of_localSymp (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (hloc :
      (∃ n : ℕ, (n = 3 ∨ 6 ≤ n) ∧ ∃ φ : LocalQuotient D d ≃* Equiv.Perm (Fin n),
        ∀ g, g ∈ LocalImages D d ↔ (φ g).IsSwap) ∨
      (∃ m : ℕ, ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
        (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
        fischerLinearModel (LocalImages D d)
          (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
          (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
        (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
        {v | Q v = 1}.ncard ≤ 2 ^ (2 * m - 1) ∧
        fischerLinearModel (LocalImages D d)
          (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
          (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))) :
    False := by
  rcases hloc with ⟨n, hn, φ, hφ⟩ | ⟨m, b, halt, hnd, hmod⟩ | ⟨m, hm, Q, hnd, hQ, hmod⟩
  · exact false_of_localSym hH hna hnot hd hn φ hφ
  · exact false_of_localSp hH hna hnot hd halt hnd hmod
  · exact false_of_localO hH hna hnot hd hm hnd hQ hmod

theorem sympResidual_of_localSymp (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (hloc : LocalSympCases (LocalQuotient D d) (LocalImages D d)) :
    SympResidual (LocalQuotient D d) (LocalImages D d) := by
  rcases hloc with ⟨n, hn, φ, hφ⟩ | ⟨m, -, b, halt, hnd, hmod⟩ |
    ⟨m, hm, Q, hnd, hplus, hmod⟩
  · by_cases h5 : n = 5
    · subst h5
      exact Or.inl ⟨φ, hφ⟩
    · exact (false_of_localSymp hH hna hnot hd (Or.inl ⟨n, by omega, φ, hφ⟩)).elim
  · exact (false_of_localSymp hH hna hnot hd (Or.inr (Or.inl ⟨m, b, halt, hnd, hmod⟩))).elim
  · by_cases hQ : {v | Q v = 1}.ncard ≤ 2 ^ (2 * m - 1)
    · exact (false_of_localSymp hH hna hnot hd
        (Or.inr (Or.inr ⟨m, by omega, Q, hnd, hQ, hmod⟩))).elim
    · exact Or.inr ⟨m, hm, Q, hnd, hplus, by omega, hmod⟩

end CFSG.Fischer.Classification
