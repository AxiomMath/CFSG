module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open Subgroup

theorem simple_of_section_irred {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {K A B : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) ↥K V) (π : ↥A → V)
    (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hπ0 : ∀ a, π a = 0 ↔ (a : G) ∈ B) (hπadd : ∀ a a', π (a * a') = π a + π a')
    (hπsurj : Function.Surjective π)
    (hρπ : ∀ (k : ↥K) (a : ↥A), ρ k (π a) = π ⟨k * a * k⁻¹, hKA _ k.2 _ a.2⟩)
    (hirred : ∀ W : Subgroup G, B ≤ W → W ≤ A → (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) →
      W = B ∨ W = A)
    (hBA : B ≤ A) (hne : B ≠ A) :
    IsSimpleModule (MonoidAlgebra (ZMod p) ↥K) ρ.asModule := by
  classical
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hπ1 : π 1 = 0 := by
    have h := hπadd 1 1
    rw [mul_one] at h
    have h' : π 1 + π 1 = π 1 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h'
  have hπinv : ∀ a, π a⁻¹ = - π a := fun a => by
    have := hπadd a⁻¹ a
    rw [inv_mul_cancel, hπ1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hV : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨a, haA, haB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hBA hne)
    have h1 : π ⟨a, haA⟩ ≠ 0 := fun h0 => haB ((hπ0 _).1 h0)
    have h2 : π ⟨a, haA⟩ ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at h2
    have h3 : π ⟨a, haA⟩ ∈ (⊥ : Submodule (ZMod p) V) := h2
    exact h1 ((Submodule.mem_bot _).1 h3)
  have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hV⟩⟩
  refine ⟨fun S => ?_⟩
  let W : Subgroup G :=
    { carrier := {g | ∃ a : ↥A, (a : G) = g ∧ π a ∈ S.toSubmodule}
      mul_mem' := by
        rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
        exact ⟨a * b, rfl, by rw [hπadd]; exact S.toSubmodule.add_mem ha hb⟩
      one_mem' := ⟨1, rfl, by rw [hπ1]; exact S.toSubmodule.zero_mem⟩
      inv_mem' := by
        rintro _ ⟨a, rfl, ha⟩
        exact ⟨a⁻¹, rfl, by rw [hπinv]; exact S.toSubmodule.neg_mem ha⟩ }
  have hBW : B ≤ W := fun b hb =>
    ⟨⟨b, hBA hb⟩, rfl, by rw [(hπ0 _).2 hb]; exact S.toSubmodule.zero_mem⟩
  have hWA : W ≤ A := by rintro _ ⟨a, rfl, -⟩; exact a.2
  have hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    rintro k hk _ ⟨a, rfl, ha⟩
    refine ⟨⟨k * a * k⁻¹, hKA k hk a a.2⟩, rfl, ?_⟩
    have h := hρπ ⟨k, hk⟩ a
    have h' := S.apply_mem_toSubmodule ⟨k, hk⟩ ha
    rw [h] at h'
    exact h'
  rcases hirred W hBW hWA hWK with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    ext v
    constructor
    · intro hv
      obtain ⟨a, rfl⟩ := hπsurj v
      have : (a : G) ∈ W := ⟨a, rfl, hv⟩
      rw [h] at this
      simp [(hπ0 a).2 this]
    · intro hv
      have hv' : v ∈ (⊥ : Submodule (ZMod p) V) := hv
      have : v = 0 := (Submodule.mem_bot _).1 hv'
      rw [this]; exact S.toSubmodule.zero_mem
  · right
    apply Subrepresentation.toSubmodule_injective
    ext v
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨a, rfl⟩ := hπsurj v
      have : (a : G) ∈ W := by rw [h]; exact a.2
      obtain ⟨a', ha', hπ'⟩ := this
      have : a' = a := Subtype.ext ha'
      rw [← this]; exact hπ'

end CFSG.GH74.GLS.Stage4.Rest.T2
