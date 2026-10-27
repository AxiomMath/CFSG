module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Trans

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem ncard_X : (omega e \ {e}).ncard = 23 := by
  rw [Set.ncard_sdiff_singleton_of_mem (e_mem_omega e), hS.ncard_omega]

theorem conj_orbit_subset_X {ω : Γ} (hω : ω ∈ omega e) (hne : ω ≠ e) :
    {y : Γ | ∃ a ∈ H₁, y = a * ω * a⁻¹} ⊆ omega e \ {e} := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨conj_mem_omega hω a, fun h => hne ?_⟩
  have hc : a * e = e * a := hS.commute_of_mem_H₁ ha
  have h' : a * ω * a⁻¹ = e := h
  calc ω = a⁻¹ * (a * ω * a⁻¹) * a := by group
    _ = a⁻¹ * e * a := by rw [h']
    _ = e := by
      rw [mul_assoc, ← hc]
      group

section Finite

variable [Finite Γ]

theorem orbit_ncard_cases {ω : Γ} (hω : ω ∈ omega e) (hne : ω ≠ e) :
    Set.ncard {y : Γ | ∃ a ∈ H₁, y = a * ω * a⁻¹} = 1 ∨
      Set.ncard {y : Γ | ∃ a ∈ H₁, y = a * ω * a⁻¹} = 23 := by
  have hωE : ω ∈ E := hS.omega_subset_E hω
  have hle : Set.ncard {y : Γ | ∃ a ∈ H₁, y = a * ω * a⁻¹} ≤ 23 := by
    rw [← hS.ncard_X]
    exact Set.ncard_le_ncard (hS.conj_orbit_subset_X hω hne) (Set.toFinite _)
  have hES : E ⊓ H₁ ≤ centralizer ({ω} : Set Γ) ⊓ H₁ := fun x hx =>
    ⟨mem_centralizer_singleton_iff.2 (hS.comm_of_mem_E hx.1 hωE), hx.2⟩
  have hrel : (centralizer ({ω} : Set Γ) ⊓ H₁).relIndex H₁ =
      (centralizer ({ω} : Set Γ)).relIndex H₁ := Subgroup.inf_relIndex_right _ _
  rw [ncard_conj_orbit] at hle ⊢
  rcases hS.eq_or_ge_relIndex inf_le_right hES with h | h
  · left
    rw [← hrel]
    exact Subgroup.relIndex_eq_one.2 (le_of_eq h.symm)
  · right
    rw [← hrel] at hle ⊢
    omega

theorem transitive {ω ω' : Γ} (hω : ω ∈ omega e) (hω' : ω' ∈ omega e) (hne : ω ≠ e)
    (hne' : ω' ≠ e) : ∃ p ∈ H₁, p * ω * p⁻¹ = ω' := by
  have key : ∃ ω₀ ∈ omega e \ {e}, Set.ncard {y : Γ | ∃ a ∈ H₁, y = a * ω₀ * a⁻¹} = 23 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hgH, hg23, hg1⟩ := hS.exists_g
    have hgE : g ∈ E := by
      rw [← hS.centralizer_omega, mem_centralizer_iff]
      intro y hy
      by_cases hye : y = e
      · rw [hye]
        exact (hS.commute_of_mem_H₁ hgH).symm
      · have h1 := (hS.orbit_ncard_cases hy hye).resolve_right (hcon y ⟨hy, hye⟩)
        obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 h1
        have hmem : g * y * g⁻¹ ∈ {y' : Γ | ∃ a ∈ H₁, y' = a * y * a⁻¹} := ⟨g, hgH, rfl⟩
        have hy_mem : y ∈ {y' : Γ | ∃ a ∈ H₁, y' = a * y * a⁻¹} :=
          ⟨1, H₁.one_mem, by simp⟩
        rw [hz] at hmem hy_mem
        have h2 : g * y * g⁻¹ = y :=
          (Set.mem_singleton_iff.1 hmem).trans (Set.mem_singleton_iff.1 hy_mem).symm
        calc y * g = g * y * g⁻¹ * g := by rw [h2]
          _ = g * y := by group
    exact hS.g_not_mem_E hg23 hg1 hgE
  obtain ⟨ω₀, hω₀, hcard⟩ := key
  have heq := Set.eq_of_subset_of_ncard_le (hS.conj_orbit_subset_X hω₀.1 hω₀.2)
    (by rw [hcard, hS.ncard_X]) (Set.toFinite _)
  have h1 : ω ∈ {y : Γ | ∃ a ∈ H₁, y = a * ω₀ * a⁻¹} := (Set.ext_iff.1 heq ω).2 ⟨hω, hne⟩
  have h2 : ω' ∈ {y : Γ | ∃ a ∈ H₁, y = a * ω₀ * a⁻¹} := (Set.ext_iff.1 heq ω').2 ⟨hω', hne'⟩
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨a', ha', rfl⟩ := h2
  exact ⟨a' * a⁻¹, H₁.mul_mem ha' (H₁.inv_mem ha), by group⟩

theorem eq_top_of_centralizer_le {Q : Subgroup Γ} (hQ : centralizer ({e} : Set Γ) ≤ Q)
    (hne : Q ≠ centralizer ({e} : Set Γ)) : Q = ⊤ := by
  obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Q, q ∉ centralizer ({e} : Set Γ) := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (fun x hx => h x hx) hQ)
  rw [eq_top_iff]
  intro γ _
  have hω1 : q * e * q⁻¹ ∈ omega e := ⟨q, rfl⟩
  have hne1 : q * e * q⁻¹ ≠ e := by
    intro h
    apply hqC
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h).symm ▸ rfl
  by_cases hγ : γ ∈ centralizer ({e} : Set Γ)
  · exact hQ hγ
  · have hω : γ * e * γ⁻¹ ∈ omega e := ⟨γ, rfl⟩
    have hne2 : γ * e * γ⁻¹ ≠ e := by
      intro h
      apply hγ
      rw [mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.1 h).symm ▸ rfl
    obtain ⟨p, hp, hpeq⟩ := hS.transitive hω1 hω hne1 hne2
    have hpC : p ∈ centralizer ({e} : Set Γ) := hS.H₁_le_centralizer hp
    have hxC : (p * q)⁻¹ * γ ∈ centralizer ({e} : Set Γ) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : (p * q)⁻¹ * γ * e * ((p * q)⁻¹ * γ)⁻¹ = e := by
        calc (p * q)⁻¹ * γ * e * ((p * q)⁻¹ * γ)⁻¹
            = (p * q)⁻¹ * (γ * e * γ⁻¹) * (p * q) := by group
          _ = (p * q)⁻¹ * (p * (q * e * q⁻¹) * p⁻¹) * (p * q) := by rw [hpeq]
          _ = e := by group
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hmem : (p * q)⁻¹ * γ ∈ Q := hQ hxC
    have hmul : p * q * ((p * q)⁻¹ * γ) = γ := by group
    have hfin : p * q * ((p * q)⁻¹ * γ) ∈ Q := Q.mul_mem (Q.mul_mem (hQ hpC) hqQ) hmem
    rwa [hmul] at hfin

end Finite

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
