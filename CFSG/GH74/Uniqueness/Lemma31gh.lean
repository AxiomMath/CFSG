module

public import CFSG.GH74.Uniqueness.Gamma
public import CFSG.GH74.Uniqueness.ProductDisconnected

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Conjugate

variable {X : Type*} [Group X]

theorem conjugate_conjugate (A : Subgroup X) (g h : X) :
    conjugate (conjugate A g) h = conjugate A (g * h) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  have : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by group
  rw [this]

theorem conjugate_one (A : Subgroup X) : conjugate A 1 = A := by
  ext x
  rw [mem_conjugate_iff]
  simp

theorem conjugate_inf (A B : Subgroup X) (g : X) :
    conjugate (A ⊓ B) g = conjugate A g ⊓ conjugate B g := by
  ext x
  simp only [mem_conjugate_iff, Subgroup.mem_inf]

theorem conjugate_eq_iff_mem_normalizer {A : Subgroup X} {g : X} :
    conjugate A g = A ↔ g ∈ normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := congrArg (fun S : Subgroup X => x ∈ S) h
    simp only [mem_conjugate_iff] at this
    exact Iff.of_eq this.symm
  · intro h
    ext x
    rw [mem_conjugate_iff]
    exact (h x).symm

theorem conjugate_eq_top_iff {A : Subgroup X} {g : X} : conjugate A g = ⊤ ↔ A = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have : g⁻¹ * x * g ∈ conjugate A g := by rw [h]; trivial
    rw [mem_conjugate_iff] at this
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  · intro h
    rw [eq_top_iff]
    intro x _
    rw [mem_conjugate_iff, h]
    trivial

theorem normalizer_conjugate (A : Subgroup X) (g : X) :
    normalizer (conjugate A g : Set X) = conjugate (normalizer (A : Set X)) g := by
  ext x
  rw [Subgroup.mem_normalizer_iff, mem_conjugate_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h w
    have := h (g⁻¹ * w * g)
    rw [mem_conjugate_iff, mem_conjugate_iff] at this
    have e1 : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    have e2 : g * (x * (g⁻¹ * w * g) * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ := by
      group
    rwa [e1, e2] at this
  · intro h y
    have := h (g * y * g⁻¹)
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have e2 : (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by
      group
    rwa [e2] at this

end Conjugate

section Omega

variable {X : Type*} [Group X] {Z : Set X} {M : Subgroup X}

@[expose] def omega (M : Subgroup X) : Set (Subgroup X) :=
  Set.range (conjugate M)

theorem mem_omega_iff {β : Subgroup X} : β ∈ omega M ↔ ∃ g : X, conjugate M g = β := Iff.rfl

theorem self_mem_omega (M : Subgroup X) : M ∈ omega M := ⟨1, conjugate_one M⟩

theorem conjugate_mem_omega {β : Subgroup X} (hβ : β ∈ omega M) (g : X) :
    conjugate β g ∈ omega M := by
  obtain ⟨k, rfl⟩ := hβ
  exact ⟨k * g, (conjugate_conjugate M k g).symm⟩

theorem IsProductDisconnected.conjugate_point (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (g : X) : IsProductDisconnected Z (conjugate M g) := by
  obtain ⟨hne, ⟨z0, hz0Z, hz0M⟩, hb, hc⟩ := h
  refine ⟨fun htop => hne (conjugate_eq_top_iff.mp htop), ⟨g⁻¹ * z0 * g, hZ.2 z0 hz0Z g, ?_⟩,
    ?_, ?_⟩
  · show g⁻¹ * z0 * g ∈ conjugate M g
    rw [mem_conjugate_iff]
    have e : g * (g⁻¹ * z0 * g) * g⁻¹ = z0 := by group
    rw [e]
    exact hz0M
  · intro z hz hzM k
    rw [mem_conjugate_iff] at hzM
    have hz' : g * z * g⁻¹ ∈ Z := by
      have := hZ.2 z hz g⁻¹
      rwa [inv_inv] at this
    have key := hb (g * z * g⁻¹) hz' hzM (g * k * g⁻¹)
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have e : g * (k⁻¹ * z * k) * g⁻¹ = (g * k * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * k * g⁻¹) := by group
    rw [e]
    exact key
  · intro u hu huM c hc'
    obtain ⟨hu2, x, hx, y, hy, hxy, rfl⟩ := hu
    rw [mem_conjugate_iff] at huM
    have hu' : (g * (x * y) * g⁻¹) ∈ productInvolutions Z := by
      have hx' : g * x * g⁻¹ ∈ Z := by
        have := hZ.2 x hx g⁻¹
        rwa [inv_inv] at this
      have hy' : g * y * g⁻¹ ∈ Z := by
        have := hZ.2 y hy g⁻¹
        rwa [inv_inv] at this
      refine ⟨?_, g * x * g⁻¹, hx', g * y * g⁻¹, hy', ?_, by group⟩
      · have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x * y)
        simpa [MulAut.conj_apply, hu2] using this
      · have e : (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        have e' : (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        rw [e, e', hxy]
    have hmem : g * c * g⁻¹ ∈ centralizer ({g * (x * y) * g⁻¹} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
      have e : g * c * g⁻¹ * (g * (x * y) * g⁻¹) = g * (c * (x * y)) * g⁻¹ := by group
      have e' : g * (x * y) * g⁻¹ * (g * c * g⁻¹) = g * ((x * y) * c) * g⁻¹ := by group
      rw [e, e', hc']
    have hcc : g * c * g⁻¹ ∈ M := hc _ hu' huM hmem
    show c ∈ conjugate M g
    rw [mem_conjugate_iff]
    exact hcc

theorem IsProductDisconnected.normalizer_eq_self (h : IsProductDisconnected Z M) :
    normalizer (M : Set X) = M := by
  obtain ⟨z, hz, hzM⟩ := h.2.1
  exact le_antisymm (h.normalizer_le le_rfl hz hzM) Subgroup.le_normalizer

theorem IsProductDisconnected.normalizer_eq_of_mem_omega (h : IsProductDisconnected Z M)
    {β : Subgroup X} (hβ : β ∈ omega M) : normalizer (β : Set X) = β := by
  obtain ⟨g, rfl⟩ := hβ
  rw [normalizer_conjugate, h.normalizer_eq_self]

theorem IsProductDisconnected.conjugate_eq_iff_mem (h : IsProductDisconnected Z M)
    {β : Subgroup X} (hβ : β ∈ omega M) {u : X} : conjugate β u = β ↔ u ∈ β := by
  rw [conjugate_eq_iff_mem_normalizer, h.normalizer_eq_of_mem_omega hβ]

theorem IsProductDisconnected.conjugate_ne_iff (h : IsProductDisconnected Z M)
    {β : Subgroup X} (hβ : β ∈ omega M) {t : X} : conjugate β t ≠ β ↔ t ∉ β :=
  not_congr (h.conjugate_eq_iff_mem hβ)

end Omega

section Lemma31

variable {X : Type*} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.exists_conj_mem_subgroup (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {u : X} (hu : u ∈ Z) : ∃ g : X, g⁻¹ * u * g ∈ M := by
  obtain ⟨S, hS⟩ := h.exists_sylow_normalizer_le hZ
  have hSM : (S : Subgroup X) ≤ M := fun x hx => hS (Subgroup.le_normalizer hx)
  obtain ⟨S', hS'⟩ := (hZ.isPGroup_zpowers hu).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S
  refine ⟨g⁻¹, ?_⟩
  have hu' : u ∈ (S' : Subgroup X) := hS' (Subgroup.mem_zpowers u)
  have : g * u * g⁻¹ ∈ ((g • S' : Sylow 2 X) : Subgroup X) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hu', by simp [MulAut.smul_def]⟩
  rw [hg] at this
  simpa using hSM this

theorem IsProductDisconnected.exists_conj_not_mem (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {u : X} (hu : u ∈ Z) : ∃ g : X, g⁻¹ * u * g ∉ M := by
  obtain ⟨g₀, hg₀⟩ := h.exists_conj_mem_subgroup hZ hu
  obtain ⟨k, hk⟩ : ∃ k : X, k ∉ M := by
    by_contra hall
    push Not at hall
    exact h.1 (eq_top_iff.mpr fun x _ => hall x)
  refine ⟨g₀ * k, fun hmem => hk ?_⟩
  have : k⁻¹ * (g₀⁻¹ * u * g₀) * k ∈ M := by
    have e : k⁻¹ * (g₀⁻¹ * u * g₀) * k = (g₀ * k)⁻¹ * u * (g₀ * k) := by group
    rw [e]
    exact hmem
  exact h.mem_of_conj_mem (hZ.2 u hu g₀) hg₀ this

theorem IsProductDisconnected.existsUnique_fixed_point (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {u : X} (hu : u ∈ Z) :
    ∃! β : Subgroup X, β ∈ omega M ∧ conjugate β u = β := by
  obtain ⟨g, hg⟩ := h.exists_conj_mem_subgroup hZ hu
  have hmem : ∀ k : X, u ∈ conjugate M k ↔ k * u * k⁻¹ ∈ M := fun k => mem_conjugate_iff
  refine ⟨conjugate M g⁻¹, ⟨⟨g⁻¹, rfl⟩, ?_⟩, ?_⟩
  · rw [h.conjugate_eq_iff_mem ⟨g⁻¹, rfl⟩, hmem]
    simpa using hg
  · rintro β ⟨hβ, hfix⟩
    obtain ⟨k, rfl⟩ := hβ
    rw [h.conjugate_eq_iff_mem ⟨k, rfl⟩, hmem] at hfix
    have hy₁ : k * u * k⁻¹ ∈ Z := by
      have := hZ.2 u hu k⁻¹
      rwa [inv_inv] at this
    have hconj : (k * g)⁻¹ * (k * u * k⁻¹) * (k * g) = g⁻¹ * u * g := by group
    have hinM : k * g ∈ M := h.mem_of_conj_mem hy₁ hfix (by rw [hconj]; exact hg)
    have hnorm : conjugate M (k * g) = M := by
      rw [conjugate_eq_iff_mem_normalizer, h.normalizer_eq_self]
      exact hinM
    calc conjugate M k = conjugate (conjugate M (k * g)) g⁻¹ := by
          rw [conjugate_conjugate]
          congr 1
          group
      _ = conjugate M g⁻¹ := by rw [hnorm]

theorem IsProductDisconnected.eq_involutions_of_isStronglyEmbedded
    (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M)
    (hM : IsStronglyEmbedded M) : Z = {x : X | orderOf x = 2} := by
  ext x
  constructor
  · exact fun hx => hZ.1 x hx
  · intro hx
    obtain ⟨z, hz, -⟩ := h.2.1
    have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded M :=
      CFSG.BenderSuzuki.isStronglyEmbedded_of_parity M
        (isStronglyEmbeddedOrder_of_isStronglyEmbedded hM)
    have hinv : ∀ y : X, orderOf y = 2 → CFSG.BenderSuzuki.PFAppendixIII.IsInvolution y := by
      intro y hy
      exact ⟨(orderOf_eq_prime_iff.mp hy).2, (orderOf_eq_prime_iff.mp hy).1⟩
    obtain ⟨g, hg⟩ := hnat.involutions_conjugate (hinv z (hZ.1 z hz)) (hinv x hx)
    rw [← hg]
    exact hZ.2 z hz g

theorem IsProductDisconnected.exists_swap (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {β γ : Subgroup X} (hβ : β ∈ omega M) (hγ : γ ∈ omega M) :
    ∃ s ∈ Z, conjugate β s = γ := by
  obtain ⟨g, rfl⟩ := hβ
  obtain ⟨k, rfl⟩ := hγ
  obtain ⟨s, hs, hsM⟩ := (h.conjugate_point hZ g).exists_mem_rightCoset hZ (g⁻¹ * k)
  refine ⟨s, hs, ?_⟩
  rw [mem_conjugate_iff] at hsM
  have hnorm : g * s * k⁻¹ ∈ normalizer (M : Set X) := by
    rw [h.normalizer_eq_self]
    have e : g * (s * (g⁻¹ * k)⁻¹) * g⁻¹ = g * s * k⁻¹ := by group
    rw [← e]
    exact hsM
  rw [← conjugate_eq_iff_mem_normalizer] at hnorm
  rw [conjugate_conjugate]
  calc conjugate M (g * s) = conjugate (conjugate M (g * s * k⁻¹)) k := by
        rw [conjugate_conjugate]
        congr 1
        group
    _ = conjugate M k := by rw [hnorm]

end Lemma31

end CFSG.GH74.Uniqueness
