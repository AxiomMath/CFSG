module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def IsNormalSetIn (𝓕 : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  (∀ X ∈ 𝓕, X ≤ K) ∧ ∀ X ∈ 𝓕, ∀ g ∈ K, X.map (MulAut.conj g).toMonoidHom ∈ 𝓕

@[expose] def sylowMembers (p : ℕ) (𝓕 : Set (Subgroup G)) (S : Subgroup G) :
    Set (Subgroup G) :=
  {X | X ∈ 𝓕 ∧ IsSylowOf p (S ⊓ X) X}

@[expose] def SylowConjLink (p : ℕ) (𝓕 : Set (Subgroup G)) (K D S S' : Subgroup G) : Prop :=
  IsSylowOf p S K ∧ IsSylowOf p S' K ∧
    ∃ X ∈ sylowMembers p 𝓕 S, X ∈ sylowMembers p 𝓕 S' ∧ D ≤ S ⊓ S' ⊓ X ∧
      ∃ x ∈ X, S' = S.map (MulAut.conj x).toMonoidHom

@[expose] def ConjVia (p : ℕ) (𝓕 : Set (Subgroup G)) (K S T : Subgroup G) : Prop :=
  Relation.ReflTransGen (SylowConjLink p 𝓕 K (S ⊓ T)) S T

@[expose] def ControlsSylowIntersections (p : ℕ) (𝓕 : Set (Subgroup G)) (K : Subgroup G) :
    Prop :=
  ∀ S T : Subgroup G, IsSylowOf p S K → IsSylowOf p T K → S ≠ T → S ⊓ T ≠ ⊥ →
    ConjVia p 𝓕 K S T

@[expose] def FusionChainStep (p : ℕ) (𝓕 : Set (Subgroup G)) (S : Subgroup G) (A : Set G)
    (h h' : G) : Prop :=
  ∃ Y ∈ sylowMembers p 𝓕 S, ∃ z ∈ Y, h' = z * h ∧ ∀ a ∈ A, h' * a * h'⁻¹ ∈ S ⊓ Y

@[expose] def StronglyControlsFusion (p : ℕ) (𝓕 : Set (Subgroup G)) (K : Subgroup G) : Prop :=
  ∀ S : Subgroup G, IsSylowOf p S K → ∀ A : Set G, A ⊆ S → (∃ a ∈ A, a ≠ 1) →
    ∀ k ∈ K, (∀ a ∈ A, k * a * k⁻¹ ∈ S) →
      ∃ h : G, Relation.ReflTransGen (FusionChainStep p 𝓕 S A) 1 h ∧
        k * h⁻¹ ∈ K ⊓ normalizer (S : Set G)

variable {p : ℕ} {𝓕 𝓕' : Set (Subgroup G)} {K D D' S S' T : Subgroup G}

theorem SylowConjLink.symm (h : SylowConjLink p 𝓕 K D S S') : SylowConjLink p 𝓕 K D S' S := by
  obtain ⟨hS, hS', X, hXS, hXS', hD, x, hx, rfl⟩ := h
  refine ⟨hS', hS, X, hXS', hXS, hD.trans_eq (by rw [inf_comm S]), x⁻¹, X.inv_mem hx, ?_⟩
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hy
    exact ⟨x * y * x⁻¹, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa [mul_assoc] using hz

theorem SylowConjLink.mono (hD : D' ≤ D) (h : SylowConjLink p 𝓕 K D S S') :
    SylowConjLink p 𝓕 K D' S S' := by
  obtain ⟨hS, hS', X, hXS, hXS', hDX, hx⟩ := h
  exact ⟨hS, hS', X, hXS, hXS', hD.trans hDX, hx⟩

theorem SylowConjLink.mono_family (h𝓕 : 𝓕 ⊆ 𝓕') (h : SylowConjLink p 𝓕 K D S S') :
    SylowConjLink p 𝓕' K D S S' := by
  obtain ⟨hS, hS', X, hXS, hXS', hDX, hx⟩ := h
  exact ⟨hS, hS', X, ⟨h𝓕 hXS.1, hXS.2⟩, ⟨h𝓕 hXS'.1, hXS'.2⟩, hDX, hx⟩

theorem ConjVia.reflTransGen_of_le (h : ConjVia p 𝓕 K S T) (hD : D ≤ S ⊓ T) :
    Relation.ReflTransGen (SylowConjLink p 𝓕 K D) S T :=
  Relation.ReflTransGen.mono (fun _ _ => SylowConjLink.mono hD) S T h

end CFSG.GroupTheory
