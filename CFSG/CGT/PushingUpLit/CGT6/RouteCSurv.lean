module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCData
public import CFSG.CGT.PushingUpLit.CGT6.RouteCLift

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped Matrix

@[expose] def Central {n : ℕ}
    (s : Matrix (Fin n) (Fin n) (ZMod 2) × Matrix (Fin n) (Fin n) (ZMod 2) ×
      Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  s.1 * s.2.1 = s.2.1 * s.1 ∧ s.1 * s.2.2 = s.2.2 * s.1

instance {n : ℕ} (s : Matrix (Fin n) (Fin n) (ZMod 2) × Matrix (Fin n) (Fin n) (ZMod 2) ×
    Matrix (Fin n) (Fin n) (ZMod 2)) : Decidable (Central s) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[expose] def AltOK {n a : ℕ} (y d t : Matrix (Fin n) (Fin n) (ZMod 2))
    (w₀ : Fin (2 * a + 1) → (Fin n → ZMod 2))
    (x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ : Fin (2 * a + 1)) : Prop :=
  Function.Injective w₀ ∧
  (∀ u : Fin n → ZMod 2, ∃ s : Finset (Fin (2 * a + 1)), ∑ i ∈ s, w₀ i = u) ∧
  x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
  (∀ i, y *ᵥ w₀ i = w₀ ((Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃) i)) ∧
  (∀ i, d *ᵥ w₀ i = w₀ ((Equiv.swap u₁ u₂ * Equiv.swap u₁ u₃) i)) ∧
  (∀ i, (t * d * t) *ᵥ w₀ i = w₀ ((Equiv.swap v₁ v₂ * Equiv.swap v₁ v₃) i)) ∧
  (∀ i, ∃ j, t *ᵥ w₀ i = w₀ j) ∧
  reachN [Equiv.swap x₁ x₂ * Equiv.swap x₁ x₃, Equiv.swap u₁ u₂ * Equiv.swap u₁ u₃,
    Equiv.swap v₁ v₂ * Equiv.swap v₁ v₃] ⟨0, by omega⟩ (2 * a + 1) = Finset.univ ∧
  (∀ u : Fin n → ZMod 2, y *ᵥ u = u → d *ᵥ u = u → (t * d * t) *ᵥ u = u → u = 0) ∧
  w₀ ⟨0, by omega⟩ ≠ 0

instance {n a : ℕ} (y d t : Matrix (Fin n) (Fin n) (ZMod 2))
    (w₀ : Fin (2 * a + 1) → (Fin n → ZMod 2))
    (x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ : Fin (2 * a + 1)) :
    Decidable (AltOK y d t w₀ x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃) := by
  unfold AltOK
  infer_instance

@[expose] def natVec4 (i : Fin 5) : Fin 4 → ZMod 2 := routeCNatVecs4.getD i.val 0

@[expose] def natVec6 (i : Fin 7) : Fin 6 → ZMod 2 := routeCNatVecs6.getD i.val 0

theorem survivor4_ok (s : Matrix (Fin 4) (Fin 4) (ZMod 2) × Matrix (Fin 4) (Fin 4) (ZMod 2) ×
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (hs : s ∈ routeCSurvivors 4) :
    Central s ∨ ∃ x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ : Fin (2 * 2 + 1),
      AltOK (a := 2) s.1 s.2.1 s.2.2 natVec4 x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ := by
  simp only [routeCSurvivors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr ⟨2, 3, 4, 1, 2, 4, 0, 2, 4, by decide⟩
  · exact Or.inr ⟨2, 3, 4, 1, 4, 2, 0, 4, 2, by decide⟩
  · exact Or.inr ⟨2, 3, 4, 0, 3, 1, 0, 1, 3, by decide⟩

theorem survivor5_ok (s : Matrix (Fin 5) (Fin 5) (ZMod 2) × Matrix (Fin 5) (Fin 5) (ZMod 2) ×
    Matrix (Fin 5) (Fin 5) (ZMod 2)) (hs : s ∈ routeCSurvivors 5) : Central s := by
  simp only [routeCSurvivors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem survivor6_ok (s : Matrix (Fin 6) (Fin 6) (ZMod 2) × Matrix (Fin 6) (Fin 6) (ZMod 2) ×
    Matrix (Fin 6) (Fin 6) (ZMod 2)) (hs : s ∈ routeCSurvivors 6) :
    Central s ∨ ∃ x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ : Fin (2 * 3 + 1),
      AltOK (a := 3) s.1 s.2.1 s.2.2 natVec6 x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ := by
  simp only [routeCSurvivors, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr ⟨0, 1, 4, 2, 4, 6, 3, 4, 5, by decide⟩

theorem survivor_nil (n : ℕ) (h4 : n ≠ 4) (h5 : n ≠ 5) (h6 : n ≠ 6) : routeCSurvivors n = [] := by
  match n, h4, h5, h6 with
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | 2, _, _, _ => rfl
  | 3, _, _, _ => rfl
  | 4, h, _, _ => exact absurd rfl h
  | 5, _, h, _ => exact absurd rfl h
  | 6, _, _, h => exact absurd rfl h
  | n + 7, _, _, _ => rfl

section Glue

variable {V : Type} [CommGroup V] {n : ℕ}

noncomputable def AltData.ofAltOK (e : V ≃* Multiplicative (Fin n → ZMod 2)) {y d t : MulAut V}
    {a : ℕ} {y₀ d₀ t₀ : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hy : (CFSG.SectionRank.Ccomm.elemAutEquivGL e y : Matrix (Fin n) (Fin n) (ZMod 2)) = y₀)
    (hd : (CFSG.SectionRank.Ccomm.elemAutEquivGL e d : Matrix (Fin n) (Fin n) (ZMod 2)) = d₀)
    (ht : (CFSG.SectionRank.Ccomm.elemAutEquivGL e t : Matrix (Fin n) (Fin n) (ZMod 2)) = t₀)
    (ht2 : t ^ 2 = 1) {w₀ : Fin (2 * a + 1) → (Fin n → ZMod 2)}
    {x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃ : Fin (2 * a + 1)}
    (h : AltOK y₀ d₀ t₀ w₀ x₁ x₂ x₃ u₁ u₂ u₃ v₁ v₂ v₃) : AltData y d t a := by
  obtain ⟨hinj, hspan, h12, h13, h23, hyw, hdw, hew, htw, hreach, hfix, hne⟩ := h
  subst hy hd ht
  exact AltData.ofMatrix e w₀ hinj hspan x₁ x₂ x₃ h12 h13 h23
    (Equiv.swap u₁ u₂ * Equiv.swap u₁ u₃) (Equiv.swap v₁ v₂ * Equiv.swap v₁ v₃)
    hyw hdw hew htw hreach hfix ht2 hne

end Glue

end CFSG.CGT.PushingUpLit.CGT6
