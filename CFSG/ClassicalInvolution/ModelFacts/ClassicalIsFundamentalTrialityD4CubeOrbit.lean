module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.Chevalley.OrthogonalFoldedWeyl

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped Matrix

section Classes

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem hclass_of_orthogonal
    (hort : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, β = α ∨ β = -α ∨ iform α β = 0)
    (a b : kernelRoots χ) (hab : (⟦a⟧ : KernelComponent χ) = ⟦b⟧) :
    (b : Fin τ.rank → ℤ) = a ∨ (b : Fin τ.rank → ℤ) = -a := by
  have h : Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) a b :=
    Quotient.exact hab
  clear hab
  induction h with
  | rel x y hxy =>
    rw [dotProduct_mulVec_eq_iform] at hxy
    rcases hort x x.2 y y.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hxy
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
    rcases ih with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  | trans x y z _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁ <;> rcases ih₂ with h₂ | h₂
    · exact Or.inl (h₂.trans h₁)
    · exact Or.inr (h₂.trans (by rw [h₁]))
    · exact Or.inr (h₂.trans (by rw [h₁]))
    · exact Or.inl (h₂.trans (by rw [h₁, neg_neg]))

end Classes

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbits_eq_singleton_of_forall_class
    (hclass : ∀ a b : kernelRoots D.χ, (⟦a⟧ : KernelComponent D.χ) = ⟦b⟧ →
      (b : Fin τ.rank → ℤ) = a ∨ (b : Fin τ.rank → ℤ) = -a) :
    ∃ O₀, D.orbits = {O₀} := by
  classical
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  obtain ⟨a, rfl⟩ := Quotient.exists_rep i₀
  obtain ⟨β₁, hβ₁h, hβ₁i⟩ : ∃ β₁ : kernelRoots D.χ, 0 < height (β₁ : Fin τ.rank → ℤ) ∧
      (⟦β₁⟧ : KernelComponent D.χ) = ⟦a⟧ := by
    by_cases ha : 0 < height (a : Fin τ.rank → ℤ)
    · exact ⟨a, ha, rfl⟩
    · have ha0 : height (a : Fin τ.rank → ℤ) < 0 :=
        lt_of_le_of_ne (not_lt.1 ha) a.2.1.height_ne_zero
      refine ⟨⟨-(a : Fin τ.rank → ℤ), IsRoot.neg a.2.1, chi_neg a.2.2⟩, ?_, ?_⟩
      · change 0 < height (-(a : Fin τ.rank → ℤ))
        rw [height_neg]
        omega
      · refine (mk_eq_of_iform_ne_zero ?_).symm
        change iform (a : Fin τ.rank → ℤ) (-(a : Fin τ.rank → ℤ)) ≠ 0
        rw [← neg_one_smul ℤ (a : Fin τ.rank → ℤ), iform_smul_right]
        have := iform_self_pos_of_isRoot a.2.1
        omega
  have hβ₁r : IsRoot τ (β₁ : Fin τ.rank → ℤ) := β₁.2.1
  have hmem₁ : (β₁ : Fin τ.rank → ℤ) ∈ componentRoots D.χ (⟦a⟧ : KernelComponent D.χ) :=
    ⟨β₁.2, hβ₁i⟩
  have hsimple₁ : (β₁ : Fin τ.rank → ℤ) ∈ simpleRoots (componentRoots D.χ
      (⟦a⟧ : KernelComponent D.χ)) := by
    refine mem_simpleRoots.2 ⟨hβ₁r, ⟨hmem₁, hβ₁h⟩, fun γ hγ δ hδ hsum => ?_⟩
    have pos : ∀ γ ∈ posRoots (componentRoots D.χ (⟦a⟧ : KernelComponent D.χ)),
        γ = (β₁ : Fin τ.rank → ℤ) := fun γ hγ => by
      obtain ⟨hγK, hγi⟩ := hγ.1
      rcases hclass ⟨γ, hγK⟩ β₁ (hγi.trans hβ₁i.symm) with h | h
      · exact h.symm
      · exfalso
        have h1 := hγ.2
        have h2 := hβ₁h
        have h' : (β₁ : Fin τ.rank → ℤ) = -γ := h
        rw [h', height_neg] at h2
        omega
    rw [pos γ hγ, pos δ hδ] at hsum
    have : (β₁ : Fin τ.rank → ℤ) = 0 := by
      have h0 : (β₁ : Fin τ.rank → ℤ) + β₁ = β₁ + 0 := by rw [add_zero]; exact hsum.symm
      exact add_left_cancel h0
    exact hβ₁r.ne_zero this
  have hi₀J : (⟦a⟧ : KernelComponent D.χ) ∈ D.J := by
    rw [hJ]
    exact ⟨0, a, ⟨a.2, rfl⟩, a, ⟨a.2, rfl⟩, by simp⟩
  have hβ₁Δ : (β₁ : Fin τ.rank → ℤ) ∈ D.simpleRootsJ := by
    rw [D.simpleRootsJ_eq]
    exact ⟨_, hi₀J, hsimple₁⟩
  have hβ₁K : (β₁ : Fin τ.rank → ℤ) ∈ kernelRoots D.χ := β₁.2
  have hmaps : ∀ m : ℕ, ∃ δ ∈ D.simpleRootsJ,
      toReal δ = (D.θ ^ m) (toReal (β₁ : Fin τ.rank → ℤ)) := by
    intro m
    induction m with
    | zero => exact ⟨_, hβ₁Δ, by simp⟩
    | succ m ih =>
      obtain ⟨δ, hδ, e⟩ := ih
      obtain ⟨δ', hδ', e'⟩ := D.mapsTo_simpleRootsJ ⟨δ, hδ, rfl⟩
      refine ⟨δ', hδ', ?_⟩
      rw [pow_succ', Module.End.mul_apply, ← e, e']
  have hpos : ∀ δ ∈ D.simpleRootsJ, 0 < height δ := fun δ hδ => by
    obtain ⟨i, -, hδi⟩ := (D.mem_simpleRootsJ_iff.1 hδ)
    exact simpleRoots_height_pos hδi
  have hall : ∀ β ∈ D.simpleRootsJ, β ∈ thetaOrbit D.θ (β₁ : Fin τ.rank → ℤ) := by
    intro β hβ
    obtain ⟨i, hiJ, hβi⟩ := D.mem_simpleRootsJ_iff.1 hβ
    have hβΨ : β ∈ componentRoots D.χ i := simpleRoots_subset hβi
    rw [hJ] at hiJ
    obtain ⟨m, α, ⟨hαK, hαi⟩, γ, ⟨hγK, hγi⟩, hθ⟩ := hiJ
    have hα : α = (β₁ : Fin τ.rank → ℤ) ∨ α = -(β₁ : Fin τ.rank → ℤ) := by
      rcases hclass β₁ ⟨α, hαK⟩ (hβ₁i.trans hαi.symm) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hγ : γ = β ∨ γ = -β := by
      obtain ⟨hβK, hβi'⟩ := hβΨ
      rcases hclass ⟨β, hβK⟩ ⟨γ, hγK⟩ (hβi'.trans hγi.symm) with h | h
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨δ, hδ, hδe⟩ := hmaps m
    have hδβ : δ = β ∨ δ = -β := by
      have e1 : toReal δ = toReal γ ∨ toReal δ = -toReal γ := by
        rcases hα with rfl | rfl
        · exact Or.inl (hδe.trans hθ)
        · refine Or.inr ?_
          rw [toReal_neg, map_neg] at hθ
          rw [hδe, ← hθ, neg_neg]
      rcases e1 with e1 | e1
      · rcases hγ with rfl | rfl
        · exact Or.inl (toReal_injective e1)
        · exact Or.inr (toReal_injective e1)
      · rcases hγ with rfl | rfl
        · exact Or.inr (toReal_injective (by rw [e1, toReal_neg]))
        · exact Or.inl (toReal_injective (by rw [e1, toReal_neg, neg_neg]))
    have hδβ' : δ = β := by
      rcases hδβ with h | h
      · exact h
      · exfalso
        have h1 := hpos δ hδ
        have h2 := hpos β hβ
        rw [h, height_neg] at h1
        omega
    exact ⟨m, by rw [← hδe, hδβ']⟩
  refine ⟨thetaOrbit D.θ (β₁ : Fin τ.rank → ℤ), ?_⟩
  ext O
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact D.thetaOrbit_eq_of_mem hβ₁K (hall β hβ)
  · rintro rfl
    exact ⟨β₁, hβ₁Δ, rfl⟩

end CFSG.ClassicalInvolution.ModelFacts
