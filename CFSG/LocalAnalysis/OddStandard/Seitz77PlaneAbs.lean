module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AffinePlane

public section

namespace CFSG.OddStandard.Seitz77

open Equiv Subgroup CFSG.Open CFSG.ComponentClassification.AS81

section Plane

variable {Ω : Type}

@[expose] def orbitLines (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) : Set (Set Ω) :=
  {ℓ | ∃ γ ∈ Γ, ℓ = (γ : Ω → Ω) '' ℓ₀}

structure GoodLine (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) (o : Ω) : Prop where
  mem : o ∈ ℓ₀
  ncard : ℓ₀.ncard = 4
  trans₂ : ∀ p₁ p₂ q₁ q₂ : Ω, p₁ ≠ p₂ → q₁ ≠ q₂ → ∃ g ∈ Γ, g p₁ = q₁ ∧ g p₂ = q₂
  stab : ∀ a ∈ ℓ₀, ∃ σ ∈ Γ, (σ : Ω → Ω) '' ℓ₀ = ℓ₀ ∧ σ o = a
  spread : ∀ δ ∈ Γ, δ o = o → ∀ b ∈ ℓ₀, b ≠ o → δ b ∈ ℓ₀ → (δ : Ω → Ω) '' ℓ₀ = ℓ₀

theorem exists_two_trans {Γ : Subgroup (Perm Ω)} {o : Ω} (h1 : ∀ p, ∃ g ∈ Γ, g o = p)
    (h2 : ∀ p q, p ≠ o → q ≠ o → ∃ g ∈ Γ, g o = o ∧ g p = q) {p₁ p₂ q₁ q₂ : Ω} (hp : p₁ ≠ p₂)
    (hq : q₁ ≠ q₂) : ∃ g ∈ Γ, g p₁ = q₁ ∧ g p₂ = q₂ := by
  obtain ⟨a, ha, hao⟩ := h1 p₁
  obtain ⟨b, hb, hbo⟩ := h1 q₁
  have hap : a⁻¹ p₂ ≠ o := fun h => hp (by
    rw [Equiv.Perm.inv_eq_iff_eq] at h
    rw [← hao, h])
  have hbq : b⁻¹ q₂ ≠ o := fun h => hq (by
    rw [Equiv.Perm.inv_eq_iff_eq] at h
    rw [← hbo, h])
  obtain ⟨c, hc, hco, hcx⟩ := h2 _ _ hap hbq
  refine ⟨b * c * a⁻¹, Γ.mul_mem (Γ.mul_mem hb hc) (Γ.inv_mem ha), ?_, ?_⟩
  · have : a⁻¹ p₁ = o := by rw [Equiv.Perm.inv_eq_iff_eq, hao]
    simp only [Perm.mul_apply, this, hco, hbo]
  · simp only [Perm.mul_apply, hcx]
    simp

namespace GoodLine

variable {Γ : Subgroup (Perm Ω)} {ℓ₀ : Set Ω} {o : Ω}

theorem exists_ne (hG : GoodLine Γ ℓ₀ o) : ∃ o' ∈ ℓ₀, o' ≠ o := by
  by_contra hcon
  push Not at hcon
  have hsub : ℓ₀ ⊆ {o} := fun x hx => hcon x hx
  have := Set.ncard_le_ncard hsub (Set.finite_singleton o)
  rw [hG.ncard, Set.ncard_singleton] at this
  omega

theorem exists_line (hG : GoodLine Γ ℓ₀ o) {p q : Ω} (hpq : p ≠ q) :
    ∃ ℓ ∈ orbitLines Γ ℓ₀, p ∈ ℓ ∧ q ∈ ℓ := by
  obtain ⟨o', ho', hne⟩ := hG.exists_ne
  obtain ⟨g, hg, hgo, hgo'⟩ := hG.trans₂ o o' p q hne.symm hpq
  exact ⟨(g : Ω → Ω) '' ℓ₀, ⟨g, hg, rfl⟩, ⟨o, hG.mem, hgo⟩, ⟨o', ho', hgo'⟩⟩

theorem eq_of_mem (hG : GoodLine Γ ℓ₀ o) {ℓ₁ ℓ₂ : Set Ω} (h₁ : ℓ₁ ∈ orbitLines Γ ℓ₀)
    (h₂ : ℓ₂ ∈ orbitLines Γ ℓ₀) {p q : Ω} (hpq : p ≠ q) (hp₁ : p ∈ ℓ₁) (hq₁ : q ∈ ℓ₁)
    (hp₂ : p ∈ ℓ₂) (hq₂ : q ∈ ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨γ₁, hγ₁, rfl⟩ := h₁
  obtain ⟨γ₂, hγ₂, rfl⟩ := h₂
  have norm : ∀ γ ∈ Γ, p ∈ (γ : Ω → Ω) '' ℓ₀ →
      ∃ γ' ∈ Γ, γ' o = p ∧ (γ' : Ω → Ω) '' ℓ₀ = (γ : Ω → Ω) '' ℓ₀ := by
    rintro γ hγ ⟨a, ha, hap⟩
    obtain ⟨σ, hσ, hσℓ, hσo⟩ := hG.stab a ha
    refine ⟨γ * σ, Γ.mul_mem hγ hσ, ?_, ?_⟩
    · show γ (σ o) = p
      rw [hσo, hap]
    · rw [show ((γ * σ : Perm Ω) : Ω → Ω) = (γ : Ω → Ω) ∘ (σ : Ω → Ω) from rfl, Set.image_comp,
        hσℓ]
  obtain ⟨γ₁', hγ₁', hγ₁'o, hγ₁'ℓ⟩ := norm γ₁ hγ₁ hp₁
  obtain ⟨γ₂', hγ₂', hγ₂'o, hγ₂'ℓ⟩ := norm γ₂ hγ₂ hp₂
  rw [← hγ₁'ℓ, ← hγ₂'ℓ]
  rw [← hγ₁'ℓ] at hq₁
  rw [← hγ₂'ℓ] at hq₂
  obtain ⟨b, hb, hbq⟩ := hq₂
  obtain ⟨b', hb', hb'q⟩ := hq₁
  have hδΓ : γ₁'⁻¹ * γ₂' ∈ Γ := Γ.mul_mem (Γ.inv_mem hγ₁') hγ₂'
  have hδo : (γ₁'⁻¹ * γ₂') o = o := by
    show γ₁'⁻¹ (γ₂' o) = o
    rw [hγ₂'o, Equiv.Perm.inv_eq_iff_eq, hγ₁'o]
  have hbo : b ≠ o := by
    rintro rfl
    exact hpq (hγ₂'o.symm.trans hbq)
  have hδb : (γ₁'⁻¹ * γ₂') b = b' := by
    show γ₁'⁻¹ (γ₂' b) = b'
    rw [hbq, Equiv.Perm.inv_eq_iff_eq, hb'q]
  have hsp := hG.spread _ hδΓ hδo b hb hbo (hδb ▸ hb')
  have e : (γ₂' : Ω → Ω) = (γ₁' : Ω → Ω) ∘ ((γ₁'⁻¹ * γ₂' : Perm Ω) : Ω → Ω) := by
    funext x
    show γ₂' x = γ₁' (γ₁'⁻¹ (γ₂' x))
    simp
  rw [e, Set.image_comp, hsp]

theorem ncard_line (hG : GoodLine Γ ℓ₀ o) {ℓ : Set Ω} (hℓ : ℓ ∈ orbitLines Γ ℓ₀) :
    ℓ.ncard = 4 := by
  obtain ⟨γ, -, rfl⟩ := hℓ
  rw [Set.ncard_image_of_injective _ γ.injective, hG.ncard]

@[expose] def line (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) (p q : Ω) : Set Ω :=
  {r | ∀ ℓ ∈ orbitLines Γ ℓ₀, p ∈ ℓ → q ∈ ℓ → r ∈ ℓ}

theorem line_eq (hG : GoodLine Γ ℓ₀ o) {ℓ : Set Ω} (hℓ : ℓ ∈ orbitLines Γ ℓ₀) {p q : Ω}
    (hpq : p ≠ q) (hp : p ∈ ℓ) (hq : q ∈ ℓ) : line Γ ℓ₀ p q = ℓ := by
  ext r
  constructor
  · intro hr
    exact hr ℓ hℓ hp hq
  · intro hr ℓ' hℓ' hp' hq'
    have := hG.eq_of_mem hℓ hℓ' hpq hp hq hp' hq'
    exact this ▸ hr

theorem isAffinePlane [Finite Ω] (hG : GoodLine Γ ℓ₀ o) (hΩ : Nat.card Ω = 16) :
    IsAffinePlane Ω (orbitLines Γ ℓ₀) := by
  have hl : ∀ p q : Ω, p ≠ q → line Γ ℓ₀ p q ∈ orbitLines Γ ℓ₀ ∧ p ∈ line Γ ℓ₀ p q ∧
      q ∈ line Γ ℓ₀ p q := by
    intro p q hpq
    obtain ⟨ℓ, hℓ, hp, hq⟩ := hG.exists_line hpq
    rw [hG.line_eq hℓ hpq hp hq]
    exact ⟨hℓ, hp, hq⟩
  have key := isAffinePlane_of_line (P := Ω) (line := line Γ ℓ₀)
    (fun p q hpq => (hl p q hpq).2) ?_ ?_ hΩ
  · have e : linesOf (line Γ ℓ₀) = orbitLines Γ ℓ₀ := by
      ext ℓ
      constructor
      · rintro ⟨p, q, hpq, rfl⟩
        exact (hl p q hpq).1
      · intro hℓ
        have h4 := hG.ncard_line hℓ
        have hfin : ℓ.Finite := Set.finite_of_ncard_pos (by omega)
        have h1 : 1 < ℓ.ncard := by omega
        obtain ⟨p, q, hp, hq, hpq⟩ := (Set.one_lt_ncard_iff hfin).mp h1
        exact ⟨p, q, hpq, (hG.line_eq hℓ hpq hp hq).symm⟩
    rw [e] at key
    exact key
  · intro p q r s hpq hrs hr hs
    obtain ⟨ℓ, hℓ, hp, hq⟩ := hG.exists_line hpq
    rw [hG.line_eq hℓ hpq hp hq] at hr hs ⊢
    rw [hG.line_eq hℓ hrs hr hs]
  · intro p q hpq
    obtain ⟨ℓ, hℓ, hp, hq⟩ := hG.exists_line hpq
    rw [hG.line_eq hℓ hpq hp hq]
    exact hG.ncard_line hℓ

theorem exists_translations [Finite Ω] (hOW : OstromWagnerAG24) (hG : GoodLine Γ ℓ₀ o)
    (hΩ : Nat.card Ω = 16) :
    ∃ T : Subgroup (Perm Ω), T ≤ Γ ∧ Γ ≤ normalizer (T : Set (Perm Ω)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 16 ∧ ∀ p q : Ω, ∃ t ∈ T, t p = q := by
  refine hOW Ω (orbitLines Γ ℓ₀) (hG.isAffinePlane hΩ) hΩ Γ ?_ hG.trans₂
  rintro g hg ℓ ⟨γ, hγ, rfl⟩
  exact ⟨g * γ, Γ.mul_mem hg hγ, by
    rw [show ((g * γ : Perm Ω) : Ω → Ω) = (g : Ω → Ω) ∘ (γ : Ω → Ω) from rfl, Set.image_comp]⟩

end GoodLine

end Plane

end CFSG.OddStandard.Seitz77
