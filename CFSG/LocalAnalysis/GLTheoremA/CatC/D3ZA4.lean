module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits


@[expose] def D3A4Levi : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ b t₁ t₂ : MulAut (D4Model K), b ^ 3 = 1 → b ∉ D4Img K → t₁ ^ 2 = 1 → t₂ ^ 2 = 1 →
      t₁ * t₂ = t₂ * t₁ → t₁ ≠ 1 → t₂ ≠ 1 → t₁ ≠ t₂ → b * t₁ = t₂ * b → b * t₂ = t₁ * t₂ * b →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → 3 ^ (4 * n) ≤ 3 * Nat.card A →
        (∀ a ∈ A, b a = a) → (∀ a ∈ A, t₁ a = a) → (∀ a ∈ A, t₂ a = a) →
        ∀ V : Subgroup (D4Model K), A ≤ V → V ≠ ⊥ → IsPGroup 3 V →
          V.map b.toMonoidHom = V → V.map t₁.toMonoidHom = V → V.map t₂.toMonoidHom = V →
          pCoreOf 3 (Subgroup.normalizer (V : Set (D4Model K))) = V →
          Subgroup.normalizer (V : Set (D4Model K)) ≠ ⊤ →
          (∃ S : Sylow 3 (D4Model K), Subgroup.normalizer ((S : Subgroup (D4Model K)) :
            Set (D4Model K)) ≤ Subgroup.normalizer (V : Set (D4Model K))) →
          (¬ ∃ S : Sylow 3 (D4Model K), (S : Subgroup (D4Model K)) = V) → False

theorem d3A4Regular_of_levi (hL : D3A4Levi) : D3A4Regular := by
  intro K _ _ n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb hf1 hf2 S
    hAS hSb hSt
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 1 ≤ n := by
    by_contra hn0
    have hn0' : n = 0 := by omega
    subst hn0'
    have h2' : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h2'
    simp at h2'
  have hBT := holds_D4Model_three hK hn
  have hA1 : A ≠ ⊥ := by
    intro hA0
    rw [hA0] at hAbig
    simp at hAbig
    have : 3 ^ (4 * n) ≥ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hAp : IsPGroup 3 A := fun a => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 a.1 a.2⟩
  have hmap : ∀ φ : MulAut (D4Model K), (∀ a ∈ A, φ a = a) → A.map φ.toMonoidHom = A := by
    intro φ hφ
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change φ a ∈ A
      rw [hφ a ha]; exact ha
    · intro hx
      exact ⟨x, hx, hφ x hx⟩
  obtain ⟨V, hAV, hV1, hVp, hVφ, hVtop, hVc, hVS⟩ := exists_canonical_parabolic 3 hBT hA1 hAp
  have hVb := hVφ b (hmap b hfb)
  have hVt₁ := hVφ t₁ (hmap t₁ hf1)
  have hVt₂ := hVφ t₂ (hmap t₂ hf2)
  by_cases hVs : ∃ S' : Sylow 3 (D4Model K), (S' : Subgroup (D4Model K)) = V
  · obtain ⟨S', hS'⟩ := hVs
    exact d3A4Borel_holds K n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb
      hf1 hf2 S' (by rw [hS']; exact hAV) (by rw [hS']; exact hVb) (by rw [hS']; exact hVt₁)
  · exact hL K n hK b t₁ t₂ hb3 hbQ ht₁2 ht₂2 hcomm h1 h2 h12 hbt₁ hbt₂ A hA hAbig hfb hf1 hf2 V hAV
      hV1 hVp hVb hVt₁ hVt₂ hVc hVtop hVS hVs

end CFSG.LocalAnalysis.GLTheoremA
