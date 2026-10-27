module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallOmegaOdd

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

@[expose] def U3CharInputThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → 3 ≤ f →
    ∀ B : Subgroup G, B ≤ T ⊔ R₂ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (2 ^ f) ^ 3 ≤ Nat.card B → B ≤ szT₁ L T ⊔ R₂

@[expose] def U3FourNormalizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (T R₂ : Subgroup G),
    U3Start G L 2 t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t 2 →
    normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem normalizer_le_of_forall_le_of_card_sylow
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hJ : ∀ B : Subgroup G, B ≤ T ⊔ R₂ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (2 ^ f) ^ 3 ≤ Nat.card B → B ≤ szT₁ L T ⊔ R₂) :
    normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := by
  intro x hx
  obtain ⟨-, -, hex, -⟩ := h.char_of_card_sylow hS2 hR
  have hHS : szT₁ L T ⊔ R₂ ≤ T ⊔ R₂ := sup_le_sup_right (szT₁_le_left L T) R₂
  have hxH : x ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => ?_
    obtain ⟨B, hBH, hBc, hwB, hBcard⟩ := hex w hw
    have hB'S : B.map (MulAut.conj x⁻¹).toMonoidHom ≤ T ⊔ R₂ := by
      rintro _ ⟨b, hb, rfl⟩
      simpa using (mem_normalizer_iff''.mp hx _).mp (hHS (hBH hb))
    have hB'c : ∀ a ∈ B.map (MulAut.conj x⁻¹).toMonoidHom,
        ∀ b ∈ B.map (MulAut.conj x⁻¹).toMonoidHom, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    have hB'card : (2 ^ f) ^ 3 ≤ Nat.card (B.map (MulAut.conj x⁻¹).toMonoidHom) := by
      rw [card_map_of_injective (MulAut.conj x⁻¹).injective, hBcard]
    exact hJ _ hB'S hB'c hB'card ⟨w, hwB, by simp⟩
  exact h.normalizer_sup_le_normalizer_szA₁_of_card_sylow hS2 hR hxH

theorem normalizer_le_of_charInputThree_of_card_sylow
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hchar : U3CharInputThree)
    (hfour : U3FourNormalizerInput) :
    normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := by
  rcases h.two_le.lt_or_eq with h3 | h2
  · exact h.normalizer_le_of_forall_le_of_card_sylow hS2 hR (hchar G L f t T R₂ h hS2 hR h3)
  · subst h2
    exact hfour G L t T R₂ h hS2 hR

section Certificates

theorem exists_move_of_charInputThree_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hchar : U3CharInputThree) (hfour : U3FourNormalizerInput)
    (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t :=
  h.exists_move_of_card_sylow hS2 hR hstar
    (h.normalizer_le_of_charInputThree_of_card_sylow hS2 hR hchar hfour) hc

theorem omega_regular_of_charInputThree_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hchar : U3CharInputThree) (hfour : U3FourNormalizerInput)
    (hdeg : U3OmegaOddDegreeInput) (hreg : U3OmegaOddRegularInput)
    (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 ∧
      HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range :=
  h.omega_regular_of_card_sylow hS2 hR hc (u3OmegaOddInput_of_degree_of_regular hdeg hreg)
    (h.exists_move_of_charInputThree_of_card_sylow hS2 hR hstar hchar hfour hc)

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
