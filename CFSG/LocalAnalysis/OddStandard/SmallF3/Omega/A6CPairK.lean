module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CRed

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {Γ : Type} [Group Γ]

@[expose] def A6CPairFactsK (Γ : Type) [Group Γ] (P Rf : Γ → Prop) (kc bound : ℕ) : Prop :=
  ∃ g0 n : Γ, g0 ^ 5 = 1 ∧ g0 ≠ 1 ∧ n * g0 * n⁻¹ = g0 ^ 2 ∧
    Nat.card (centralizer ({g0} : Set Γ)) = kc ∧
    ∀ a : Γ, P a → a * a = 1 → (a * g0) ^ 4 = 1 → (g0 * a * g0) ^ 5 = 1 →
      (Nat.card (centralizer ({a, g0} : Set Γ)) ≤ bound ∧
        ∀ c ∈ centralizer ({a, g0} : Set Γ), c * c = 1) ∧
      ∀ y₁ ∈ centralizer ({a, g0} : Set Γ), ∀ y₂ ∈ centralizer ({a, g0} : Set Γ),
        y₁ ≠ y₂ → y₁ ≠ 1 → y₂ ≠ 1 → Rf y₁ ∨ Rf y₂ ∨ Rf (y₁ * y₂)

theorem A6CPairFactsK.toFacts {P Rf : Γ → Prop} {kc bound : ℕ}
    (F : A6CPairFactsK Γ P Rf kc bound) : A6CPairFacts Γ P kc bound := by
  obtain ⟨g0, n, h5, h1, hn, hkc, hF⟩ := F
  exact ⟨g0, n, h5, h1, hn, hkc, fun a hP haa ha4 hga => (hF a hP haa ha4 hga).1⟩

theorem a6c_centralizer_A6K [Finite Γ] {P Rf : Γ → Prop} {kc bound : ℕ}
    (hP : ∀ a δ : Γ, P a → P (δ * a * δ⁻¹)) (hRf : ∀ a δ : Γ, Rf a → Rf (δ * a * δ⁻¹))
    (hΓ : ¬ 25 ∣ Nat.card Γ) (F : A6CPairFactsK Γ P Rf kc bound) (A : Subgroup Γ)
    (e : A ≃* alternatingGroup (Fin 6)) (hA : ∀ a ∈ A, a * a = 1 → a ≠ 1 → P a) :
    ∀ y₁ ∈ centralizer (A : Set Γ), ∀ y₂ ∈ centralizer (A : Set Γ),
      y₁ ≠ y₂ → y₁ ≠ 1 → y₂ ≠ 1 → Rf y₁ ∨ Rf y₂ ∨ Rf (y₁ * y₂) := by
  unfold A6CPairFactsK at F
  obtain ⟨g0, n, hg0, hg1, hn, _, hF⟩ := F
  obtain ⟨a, ha, x, hx, haa, ha1, hx5, hx1, hax4, hxax5⟩ := a6c_exists_std_pair e
  obtain ⟨δ, hδ⟩ := a6c_exists_conj_g0 hΓ hg0 hg1 hn hx5 hx1
  set a' : Γ := δ * a * δ⁻¹ with ha'def
  have hPa : P a := hA a ha haa ha1
  have hPa' : P a' := by simpa [ha'def] using hP a δ hPa
  have ha'a' : a' * a' = 1 := by
    have h : a' * a' = δ * (a * a) * δ⁻¹ := by rw [ha'def]; group
    rw [h, haa]; group
  have ha'g0 : (a' * g0) ^ 4 = 1 := by
    have h : a' * g0 = δ * (a * x) * δ⁻¹ := by rw [ha'def, ← hδ]; group
    rw [h, conj_pow, hax4]; group
  have hg0a'g0 : (g0 * a' * g0) ^ 5 = 1 := by
    have h : g0 * a' * g0 = δ * (x * a * x) * δ⁻¹ := by rw [ha'def, ← hδ]; group
    rw [h, conj_pow, hxax5]; group
  have hmem : ∀ c : Γ, c ∈ centralizer (A : Set Γ) →
      δ * c * δ⁻¹ ∈ centralizer ({a', g0} : Set Γ) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    have hca : a * c = c * a := (Subgroup.mem_centralizer_iff).mp hc a ha
    have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff).mp hc x hx
    rcases hh with rfl | rfl
    · rw [ha'def]
      have e1 : δ * a * δ⁻¹ * (δ * c * δ⁻¹) = δ * (a * c) * δ⁻¹ := by group
      have e2 : δ * c * δ⁻¹ * (δ * a * δ⁻¹) = δ * (c * a) * δ⁻¹ := by group
      rw [e1, e2, hca]
    · rw [← hδ]
      have e1 : (δ * x * δ⁻¹) * (δ * c * δ⁻¹) = δ * (x * c) * δ⁻¹ := by group
      have e2 : δ * c * δ⁻¹ * (δ * x * δ⁻¹) = δ * (c * x) * δ⁻¹ := by group
      rw [e1, e2, hcx]
  have hback : ∀ z : Γ, Rf (δ * z * δ⁻¹) → Rf z := by
    intro z hz
    have h := hRf _ δ⁻¹ hz
    rwa [show δ⁻¹ * (δ * z * δ⁻¹) * δ⁻¹⁻¹ = z by group] at h
  have hconj1 : ∀ z : Γ, z ≠ 1 → δ * z * δ⁻¹ ≠ 1 := by
    intro z hz h
    apply hz
    calc z = δ⁻¹ * (δ * z * δ⁻¹) * δ := by group
      _ = 1 := by rw [h]; group
  intro y₁ hy₁ y₂ hy₂ hne h1 h2
  have hne' : δ * y₁ * δ⁻¹ ≠ δ * y₂ * δ⁻¹ := by
    intro h
    apply hne
    calc y₁ = δ⁻¹ * (δ * y₁ * δ⁻¹) * δ := by group
      _ = δ⁻¹ * (δ * y₂ * δ⁻¹) * δ := by rw [h]
      _ = y₂ := by group
  have key := (hF a' hPa' ha'a' ha'g0 hg0a'g0).2 _ (hmem y₁ hy₁) _ (hmem y₂ hy₂) hne'
    (hconj1 y₁ h1) (hconj1 y₂ h2)
  rcases key with k | k | k
  · exact Or.inl (hback y₁ k)
  · exact Or.inr (Or.inl (hback y₂ k))
  · refine Or.inr (Or.inr (hback (y₁ * y₂) ?_))
    rwa [show δ * (y₁ * y₂) * δ⁻¹ = δ * y₁ * δ⁻¹ * (δ * y₂ * δ⁻¹) by group]

theorem a6c_redK {X R : Type} [Group X] [Group R] [Finite X] [Finite Γ]
    {P Rf : Γ → Prop} {kc bound : ℕ} (hP : ∀ a δ : Γ, P a → P (δ * a * δ⁻¹))
    (hRf : ∀ a δ : Γ, Rf a → Rf (δ * a * δ⁻¹))
    (hΓ : ¬ 25 ∣ Nat.card Γ) (hkc : kc ∣ 40) (F : A6CPairFactsK Γ P Rf kc bound)
    (φ : X →* Γ) (ψ : R →* Γ) (e : X ⧸ center X ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (center X))) (hker : ∀ x : X, φ x = 1 → x ∈ center X)
    (hA : ∀ a ∈ φ.range, a * a = 1 → a ≠ 1 → P a)
    (hcomm : ∀ (x : X) (r : R), φ x * ψ r = ψ r * φ x) :
    (Nat.card ψ.range ≤ bound ∧ ∀ c ∈ ψ.range, c * c = 1) ∧
      ∀ y₁ ∈ ψ.range, ∀ y₂ ∈ ψ.range, y₁ ≠ y₂ → y₁ ≠ 1 → y₂ ≠ 1 →
        Rf y₁ ∨ Rf y₂ ∨ Rf (y₁ * y₂) := by
  refine ⟨a6c_red hP hΓ hkc F.toFacts φ ψ e hodd hker hA hcomm, ?_⟩
  obtain ⟨e'⟩ := a6c_range_equiv_A6 φ e hodd hker hΓ
    (fun ξ hξ => (a6c_card_centralizer_of_orderOf hΓ F.toFacts hξ) ▸ hkc)
  have hle : ψ.range ≤ centralizer (φ.range : Set Γ) := by
    rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact hcomm x r
  intro y₁ h₁ y₂ h₂ hne h1 h2
  exact a6c_centralizer_A6K hP hRf hΓ F φ.range e' hA y₁ (hle h₁) y₂ (hle h₂) hne h1 h2

end CFSG.OddStandard.SmallF3.Omega
