module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Sec3S4

open Equiv

theorem mem_iff_sign_eq_one {G : Type*} [Group G] (e : G ≃* Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) (x : G) : x ∈ R ↔ Perm.sign (e x) = 1 := by
  have h1 : (R.comap e.symm.toMonoidHom).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ e.symm.surjective, hR]
  have h2 := Perm.eq_alternatingGroup_of_index_eq_two h1
  have h3 : e x ∈ R.comap e.symm.toMonoidHom ↔ x ∈ R := by
    simp [Subgroup.mem_comap]
  rw [← h3, h2, Perm.mem_alternatingGroup]

theorem outer_conj_perm :
    ∀ a b : Perm (Fin 4), a * a = 1 → b * b = 1 → Perm.sign a ≠ 1 → Perm.sign b ≠ 1 →
      ∃ g : Perm (Fin 4), g * a * g⁻¹ = b := by
  decide +kernel

theorem cent_card_perm :
    ∀ t : Perm (Fin 4), t * t = 1 → Perm.sign t ≠ 1 →
      (Finset.univ.filter (fun x : Perm (Fin 4) => Perm.sign x = 1 ∧ x * t = t * x)).card = 2 := by
  decide +kernel

theorem twist_perm :
    ∀ t : Perm (Fin 4), t * t = 1 → Perm.sign t ≠ 1 →
      ∃ d₀ d₁ : Perm (Fin 4), Perm.sign d₀ = 1 ∧ Perm.sign d₁ = 1 ∧ d₀ ≠ 1 ∧ d₀ * d₀ = 1 ∧
        d₁ * d₁ = 1 ∧ d₀ * d₁ = d₁ * d₀ ∧ t * d₀ * t⁻¹ = d₀ ∧ t * d₁ * t⁻¹ = d₀ * d₁ := by
  decide +kernel

theorem outer_involution_perm {G : Type*} [Group G] (e : G ≃* Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) {g : G} (hg : g * g = 1) (hgR : g ∉ R) :
    e g * e g = 1 ∧ Perm.sign (e g) ≠ 1 :=
  ⟨by rw [← map_mul, hg, map_one], fun h => hgR ((mem_iff_sign_eq_one e R hR g).2 h)⟩

theorem twist_klein {G : Type*} [Group G] (e : G ≃* Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) {τ : G} (hτ : τ * τ = 1) (hτR : τ ∉ R) :
    ∃ d₀ ∈ R, ∃ d₁ ∈ R, d₀ ≠ 1 ∧ d₀ * d₀ = 1 ∧ d₁ * d₁ = 1 ∧ d₀ * d₁ = d₁ * d₀ ∧
      τ * d₀ * τ⁻¹ = d₀ ∧ τ * d₁ * τ⁻¹ = d₀ * d₁ := by
  obtain ⟨hτ', hτS⟩ := outer_involution_perm e R hR hτ hτR
  obtain ⟨d₀, d₁, h0, h1, hne, hsq0, hsq1, hcomm, hc0, hc1⟩ := twist_perm (e τ) hτ' hτS
  refine ⟨e.symm d₀, ?_, e.symm d₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_iff_sign_eq_one e R hR]
    simpa using h0
  · rw [mem_iff_sign_eq_one e R hR]
    simpa using h1
  · intro h
    exact hne (by simpa using congrArg e h)
  · apply e.injective
    simpa using hsq0
  · apply e.injective
    simpa using hsq1
  · apply e.injective
    simpa using hcomm
  · apply e.injective
    simpa using hc0
  · apply e.injective
    simpa using hc1

end Sec3S4

theorem s4_outer_conj {G : Type*} [Group G] (e : G ≃* Equiv.Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) {a b : G} (ha : a * a = 1) (hb : b * b = 1) (haR : a ∉ R) (hbR : b ∉ R) :
    ∃ g : G, g * a * g⁻¹ = b := by
  obtain ⟨ha', haS⟩ := Sec3S4.outer_involution_perm e R hR ha haR
  obtain ⟨hb', hbS⟩ := Sec3S4.outer_involution_perm e R hR hb hbR
  obtain ⟨g, hg⟩ := Sec3S4.outer_conj_perm (e a) (e b) ha' hb' haS hbS
  refine ⟨e.symm g, e.injective ?_⟩
  simpa using hg

theorem s4_cent_card {G : Type*} [Group G] (e : G ≃* Equiv.Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) {g : G} (hg : g * g = 1) (hgR : g ∉ R) :
    Nat.card ↥(R ⊓ Subgroup.centralizer ({g} : Set G)) = 2 := by
  obtain ⟨hg', hgS⟩ := Sec3S4.outer_involution_perm e R hR hg hgR
  have hcard := Sec3S4.cent_card_perm (e g) hg' hgS
  let E : ↥(R ⊓ Subgroup.centralizer ({g} : Set G)) ≃
      {x : Equiv.Perm (Fin 4) // Equiv.Perm.sign x = 1 ∧ x * e g = e g * x} :=
    e.toEquiv.subtypeEquiv fun x => by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Sec3S4.mem_iff_sign_eq_one e R hR x]
      refine and_congr Iff.rfl ?_
      change x * g = g * x ↔ e x * e g = e g * e x
      rw [← map_mul, ← map_mul]
      exact e.injective.eq_iff.symm
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

theorem s4_twist {G : Type*} [Group G] (e : G ≃* Equiv.Perm (Fin 4)) (R : Subgroup G)
    (hR : R.index = 2) {τ : G} (hτ : τ * τ = 1) (hτR : τ ∉ R) :
    ∃ d₀ ∈ R, ∃ d₁ ∈ R, d₀ ≠ 1 ∧ d₀ * d₀ = 1 ∧ τ * d₀ * τ⁻¹ = d₀ ∧ τ * d₁ * τ⁻¹ = d₀ * d₁ := by
  obtain ⟨d₀, h₀, d₁, h₁, hne, hsq, -, -, hc₀, hc₁⟩ := Sec3S4.twist_klein e R hR hτ hτR
  exact ⟨d₀, h₀, d₁, h₁, hne, hsq, hc₀, hc₁⟩

namespace Sec3S4

alias s4_outer_conj := CFSG.GH74.GLS.IVK.Proofs2.s4_outer_conj

alias s4_cent_card := CFSG.GH74.GLS.IVK.Proofs2.s4_cent_card

alias s4_twist := CFSG.GH74.GLS.IVK.Proofs2.s4_twist

end Sec3S4

end CFSG.GH74.GLS.IVK.Proofs2
