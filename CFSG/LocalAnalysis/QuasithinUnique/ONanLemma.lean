module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBalancedMain
public import CFSG.LocalAnalysis.QuasithinUnique.ONanComplement
public import CFSG.LocalAnalysis.QuasithinUnique.ONanHyperplane

public section

namespace CFSG.QuasithinUnique.ONan

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def IsIrreducible (X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsTransitiveNonzero (X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w

@[expose] def IsTransitiveOnSummand (R : Subgroup (V ≃ₗ[ZMod 2] V))
    (A C : Submodule (ZMod 2) V) : Prop :=
  (∀ r ∈ R, ∀ a ∈ A, r a ∈ A) ∧ (∀ r ∈ R, ∀ c ∈ C, r c = c) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ 0 → b ≠ 0 → ∃ r ∈ R, r a = b

@[expose] def image (x : V ≃ₗ[ZMod 2] V) (C : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  C.map (x : V →ₗ[ZMod 2] V)

@[expose] def orbit (X : Subgroup (V ≃ₗ[ZMod 2] V)) (C : Submodule (ZMod 2) V) :
    Set (Submodule (ZMod 2) V) :=
  {D | ∃ x ∈ X, image x C = D}

@[expose] def IsTI (X : Subgroup (V ≃ₗ[ZMod 2] V)) (C : Submodule (ZMod 2) V) : Prop :=
  ∀ x ∈ X, C ⊓ image x C ≠ ⊥ → image x C = C

theorem binary_hyperplane_transitivity (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (hRX : R ≤ X)
    (hX : IsIrreducible X) (A C : Submodule (ZMod 2) V) (hAC : IsCompl A C)
    (hA : 2 ≤ Module.finrank (ZMod 2) A) (hC : Module.finrank (ZMod 2) C = 1)
    (hR : IsTransitiveOnSummand R A C) : IsTransitiveNonzero X :=
  hyperplane_transitive ⟨hRX, hAC, hR.1, hR.2.1, hR.2.2⟩ hX hA hC

theorem binary_larger_complement_transitivity (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (hRX : R ≤ X)
    (hX : IsIrreducible X) (A C : Submodule (ZMod 2) V) (hAC : IsCompl A C)
    (hC : 2 ≤ Module.finrank (ZMod 2) C)
    (hAC' : Module.finrank (ZMod 2) C < Module.finrank (ZMod 2) A)
    (hR : IsTransitiveOnSummand R A C) : IsTransitiveNonzero X :=
  larger_complement_transitive ⟨hRX, hAC, hR.1, hR.2.1, hR.2.2⟩ hX hC hAC'

theorem binary_deficiency_one_spread_completion (r : ℕ) (hr : 1 ≤ r)
    (hV : Module.finrank (ZMod 2) V = 2 * r) (D : Fin (2 ^ r) → Submodule (ZMod 2) V)
    (hD : ∀ i, Module.finrank (ZMod 2) (D i) = r) (hDD : ∀ i j, i ≠ j → D i ⊓ D j = ⊥) :
    ∃ Z : Submodule (ZMod 2) V, Module.finrank (ZMod 2) Z = r ∧
      ∀ v : V, v ∈ Z ↔ (v = 0 ∨ ∀ i, v ∉ D i) := by
  have _ := hr
  exact spread_completion_fin r hV D hD hDD

theorem balanced_TI_cyclic_normalizer (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (hRX : R ≤ X)
    (hX : IsIrreducible X) (A C : Submodule (ZMod 2) V) (hAC : IsCompl A C)
    (hC : 2 ≤ Module.finrank (ZMod 2) C)
    (hAC' : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) C)
    (hR : IsTransitiveOnSummand R A C) (hRcyc : IsCyclic R)
    (hRfree : ∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1)
    (hTI : IsTI X C) (hRnorm : ∀ x ∈ X, image x C = C → ∀ r ∈ R, x * r * x⁻¹ ∈ R) :
    orbit X C = {C, A} := by
  have _ := hRcyc
  have hB : Balanced X R A C :=
    ⟨⟨hRX, hAC, hR.1, hR.2.1, hR.2.2⟩, hX, hC, hAC', hRfree, hTI, hRnorm⟩
  ext D
  exact hB.exists_smul_iff D

theorem onan_irreducible_intransitive_TI (X R : Subgroup (V ≃ₗ[ZMod 2] V)) (hRX : R ≤ X)
    (hX : IsIrreducible X) (hXt : ¬ IsTransitiveNonzero X) (A C : Submodule (ZMod 2) V)
    (hAC : IsCompl A C) (hA : 2 ≤ Module.finrank (ZMod 2) A) (hC0 : C ≠ ⊥) (hCV : C ≠ ⊤)
    (hR : IsTransitiveOnSummand R A C) (hRcyc : IsCyclic R)
    (hRfree : ∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1)
    (hTI : IsTI X C) (hRnorm : ∀ x ∈ X, image x C = C → ∀ r ∈ R, x * r * x⁻¹ ∈ R) :
    (orbit X C).ncard = 2 := by
  have hS : Setting X R A C := ⟨hRX, hAC, hR.1, hR.2.1, hR.2.2⟩
  have hCfin : 1 ≤ Module.finrank (ZMod 2) C := Submodule.one_le_finrank_iff.mpr hC0
  by_cases hC1 : Module.finrank (ZMod 2) C = 1
  · exact absurd (binary_hyperplane_transitivity X R hRX hX A C hAC hA hC1 hR) hXt
  · have hC2 : 2 ≤ Module.finrank (ZMod 2) C := by omega
    have hnot : ¬ ∀ x ∈ X, ∀ v ∈ C, x v ∈ C := fun hinv => (hX C hinv).elim hC0 hCV
    obtain ⟨x, hx, hxC⟩ : ∃ x ∈ X, image x C ≠ C := by
      by_contra hcon
      apply hnot
      intro x hx v hv
      have h1 : image x C = C := by
        by_contra hne
        exact hcon ⟨x, hx, hne⟩
      have h2 : x v ∈ image x C := ⟨v, hv, rfl⟩
      rwa [h1] at h2
    have hinf : C ⊓ image x C = ⊥ := by
      by_contra hne
      exact hxC (hTI x hx hne)
    have hdim : Module.finrank (ZMod 2) C ≤ Module.finrank (ZMod 2) A := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq C (image x C)
      rw [hinf, finrank_bot] at h1
      have h2 : Module.finrank (ZMod 2) (image x C) = Module.finrank (ZMod 2) C :=
        LinearEquiv.finrank_map_eq x C
      have h3 := Submodule.finrank_le (C ⊔ image x C)
      have h4 := hS.finrank_space
      omega
    by_cases hlt : Module.finrank (ZMod 2) C < Module.finrank (ZMod 2) A
    · exact absurd (binary_larger_complement_transitivity X R hRX hX A C hAC hC2 hlt hR) hXt
    · have hAC' : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) C := by omega
      have horb := balanced_TI_cyclic_normalizer X R hRX hX A C hAC hC2 hAC' hR hRcyc hRfree
        hTI hRnorm
      rw [horb]
      have hne : C ≠ A := by
        intro h
        have h1 : A ⊓ C = ⊥ := hAC.inf_eq_bot
        rw [← h, inf_idem] at h1
        exact hC0 h1
      exact Set.ncard_pair hne

end CFSG.QuasithinUnique.ONan
