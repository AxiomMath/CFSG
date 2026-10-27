module

public import CFSG.ClassicalInvolution.Asc77.AscSix66

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def Core66 (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) →
    (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) → (∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) →
      (∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J') →
        ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B →
          (∀ C₁ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s A},
            ∀ C₂ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s A}, C₁ ≠ C₂ → Commutes C₁ C₂) →
          (∀ C₁ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s B},
            ∀ C₂ ∈ {C : Subgroup G | ∃ s ∈ S, C = conjSub s B}, C₁ ≠ C₂ → Commutes C₁ C₂) →
            Commutes A B

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem orbit_commutes_cyc {n : ℕ}
    (ih : ∀ m < n, ∀ S' : Subgroup G, Nat.card S' = m → IsPGroup 2 S' →
      ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S') → (∀ A ∈ Δ, ∀ s ∈ S', conjSub s A ∈ Δ) →
        (∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) →
        (∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J') →
          ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B)
    {S : Subgroup G} (hSn : Nat.card S = n) (hS : IsPGroup 2 S) {Δ : Set (Subgroup G)}
    (hΔinv : ∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ)
    (hcyc : ∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A)
    (hpair : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J')
    {C : Subgroup G} (hC : C ∈ Δ) (hCS : C < S) :
    ∀ C₁ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C},
      ∀ C₂ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C}, C₁ ≠ C₂ → Commutes C₁ C₂ := by
  obtain ⟨hXS, hXlt⟩ := card_biSup_conj_lt hS hCS
  have hmemΔ : ∀ C' ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C}, C' ∈ Δ := by
    rintro _ ⟨s, hs, rfl⟩
    exact hΔinv C hC s hs
  refine ih _ (hSn ▸ hXlt) (⨆ s ∈ S, conjSub s C) rfl (hS.to_le hXS)
    {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C} ?_ ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact le_iSup₂_of_le s hs le_rfl
  · rintro _ ⟨s, hs, rfl⟩ x hx
    exact ⟨x * s, S.mul_mem (hXS hx) hs, conjSub_mul x s C ▸ rfl⟩
  · exact fun C' hC' => hcyc C' (hmemΔ C' hC')
  · exact fun C₁ h₁ C₂ h₂ hne => hpair C₁ (hmemΔ C₁ h₁) C₂ (hmemΔ C₂ h₂) hne

theorem cyc66_of_core66 (hΩ : HypOmegaMod p f Ω) (hcore : Core66 Ω) : Cyc66 Ω := by
  have key : ∀ n : ℕ, ∀ S : Subgroup G, Nat.card S = n → IsPGroup 2 S →
      ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) → (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) →
        (∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) →
        (∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J') →
          ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro S hSn hS Δ hΔS hΔinv hcyc hpair A hA B hB hne
    have hlt : ∀ A B : Subgroup G, A ∈ Δ → B ∈ Δ → A ≠ B → A < S := by
      intro A B hA hB hne
      refine lt_of_le_of_ne (hΔS A hA) ?_
      intro hAS
      obtain ⟨J, hJ, J', hJ', hJJ', hAJ, hBJ'⟩ := hpair A hA B hB hne
      have hBA : B ≤ A := hAS ▸ hΔS B hB
      have hBJ : B ≤ J := hBA.trans hAJ
      have hB2 : IsPGroup 2 ↥B := (hS.to_le (hΔS B hB))
      exact hJJ' (hΩ.eq_of_le_of_le hJ hJ' hB2 (hcyc B hB).2 hBJ hBJ')
    have hAS := hlt A B hA hB hne
    have hBS := hlt B A hB hA (Ne.symm hne)
    refine hcore S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne ?_ ?_
    · exact orbit_commutes_cyc ih hSn hS hΔinv hcyc hpair hA hAS
    · exact orbit_commutes_cyc ih hSn hS hΔinv hcyc hpair hB hBS
  intro S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne
  exact key _ S rfl hS Δ hΔS hΔinv hcyc hpair A hA B hB hne

variable (p f)

theorem l6_6ii_of_core66
    (hcore : p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → Core66 Ω) : L6_6ii p f :=
  fun hp hq G _ _ Ω hΩ => cyc66_of_core66 hΩ (hcore hp hq G Ω hΩ)

theorem l6_6iiAEmpty_of_core66
    (hcore : p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → (∀ K ∈ Ω, AEmpty Ω K) → Core66 Ω) : L6_6iiAEmpty p f :=
  fun hp hq G _ _ Ω hΩ hA => cyc66_of_core66 hΩ (hcore hp hq G Ω hΩ hA)

end CFSG.ClassicalInvolution.Asc77
