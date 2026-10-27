module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Milestones.CL_LIT_Fischer_3T_existence_uniqueness

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open Matrix

theorem pair_of_hasType {k : Fin 3} {X : Type} [Group X] {E : Set X} (h : HasType k X E) :
    Pair X E := by
  unfold HasType at h
  split at h
  · exact h.1
  · exact h.1
  · exact h.1

theorem exists_mulEquiv_carrier
    {G : Type} [Group G] {D : Set G} (hH : Hyp G D) (k : Fin 3)
    (hk : HasType k G D) :
    ∃ φ : G ≃* Carrier k, Pair (Carrier k) (φ '' D) ∧
      ∀ E : Set (Carrier k), Pair (Carrier k) E → E = φ '' D := by
  obtain ⟨-, -, D₀, hD₀, huniq, -, hiso⟩ :=
    CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full k
  obtain ⟨φ, hφ⟩ := hiso G D hH.pair hH.center hH.simple hk
  have hP₀ : Pair (Carrier k) D₀ := pair_of_hasType hD₀
  refine ⟨φ, hφ ▸ hP₀, fun E hE => ?_⟩
  rw [hφ]
  exact huniq E hE

theorem pinned_of_statement
    (h : Statement) {G : Type} [Group G] {D : Set G} (hH : Hyp G D) :
    ClassicalConclusion G D ∨
      (∃ φ : G ≃* CFSG.Blueprint.NativeSporadic.Fi22,
        Pair CFSG.Blueprint.NativeSporadic.Fi22 (φ '' D) ∧
          ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi22,
            Pair CFSG.Blueprint.NativeSporadic.Fi22 E → E = φ '' D) ∨
      (∃ φ : G ≃* CFSG.Blueprint.NativeSporadic.Fi23,
        Pair CFSG.Blueprint.NativeSporadic.Fi23 (φ '' D) ∧
          ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi23,
            Pair CFSG.Blueprint.NativeSporadic.Fi23 E → E = φ '' D) ∨
      (∃ φ : G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime,
        Pair (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) (φ '' D) ∧
          ∀ E : Set (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime),
            Pair (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) E → E = φ '' D) := by
  rcases h G D hH with hc | ⟨k, hk⟩
  · exact Or.inl hc
  · right
    obtain ⟨φ, hφ⟩ := exists_mulEquiv_carrier hH k hk
    match k, φ, hφ with
    | ⟨0, _⟩, φ, hφ => exact Or.inl ⟨φ, hφ⟩
    | ⟨1, _⟩, φ, hφ => exact Or.inr (Or.inl ⟨φ, hφ⟩)
    | ⟨2, _⟩, φ, hφ => exact Or.inr (Or.inr ⟨φ, hφ⟩)

end CFSG.Fischer.Classification
