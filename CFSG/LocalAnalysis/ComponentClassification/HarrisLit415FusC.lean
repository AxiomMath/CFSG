module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415FusB

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem exists_conj_t_mul_beta (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X}
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) {α g₀ : X}
    (hX : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g₀).toMonoidHom =
      closure {α, z₁, t * z₁ * t⁻¹})
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    ∃ g : X, g * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹ = z₁ := by
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hz₁Y : z₁ ∈ closure ({α, z₁, t * z₁ * t⁻¹} : Set X) := subset_closure (by simp)
  obtain ⟨x, hxdef⟩ : ∃ x, x = g₀⁻¹ * z₁ * g₀ := ⟨_, rfl⟩
  have hxX : x ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rw [hxdef]
    exact L415.conj_mem_of_map_conj hX hz₁Y
  have hx : g₀ * x * g₀⁻¹ = z₁ := by rw [hxdef]; group
  rcases hc.mem_X_cases hxX with h1 | h1
  · exfalso
    rcases hc.mem_beta_z_cases h1 with h2 | h2 | h2 | h2
    · apply hc.z₁_ne
      have h3 : z₁ = 1 := by rw [← hx, h2]; group
      rw [h3]
      group
    · rw [h2] at hx
      exact hnβ g₀ hx
    · exact hc.not_conj_z_of hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hX g₀⁻¹ (by
        rw [inv_inv, ← hxdef, h2])
    · apply hnβ (g₀ * τ)
      calc g₀ * τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (g₀ * τ)⁻¹ =
          g₀ * (τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹) * g₀⁻¹ := by group
        _ = g₀ * x * g₀⁻¹ := by rw [hτβ, h2]
        _ = z₁ := hx
  · have h2 : x = t * (t * x) := by rw [← mul_assoc t t, ht2, one_mul]
    rcases hc.mem_beta_z_cases h1 with h3 | h3 | h3 | h3 <;> rw [h3] at h2
    · exfalso
      exact hc.conj_t_ne_z₁ g₀ (by rw [← hx, h2, mul_one])
    · exact ⟨g₀, by rw [← h2]; exact hx⟩
    · exfalso
      apply hc.conj_t_ne_z₁ (g₀ * z₁)
      calc g₀ * z₁ * t * (g₀ * z₁)⁻¹ = g₀ * (z₁ * t * z₁⁻¹) * g₀⁻¹ := by group
        _ = g₀ * x * g₀⁻¹ := by rw [hc.z₁_conj_t, h2]
        _ = z₁ := hx
    · refine ⟨g₀ * z₁, ?_⟩
      calc g₀ * z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * (g₀ * z₁)⁻¹ =
          g₀ * (z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹) * g₀⁻¹ := by group
        _ = g₀ * x * g₀⁻¹ := by rw [hc.z₁_conj_t_mul, h2]
        _ = z₁ := hx

theorem fusion_415 (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X}
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) {α g₀ : X}
    (hX : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g₀).toMonoidHom =
      closure {α, z₁, t * z₁ * t⁻¹})
    (hstar : ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹)
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    (∀ g : X, g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} →
      g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z) ∧
      (∃ g : X, g * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g⁻¹ = z₁) ∧
      twoPart (centralizer ({z₁} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) := by
  have hσ := hs.setup
  obtain ⟨g₁, hg₁⟩ := hc.exists_conj_t_mul_beta hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hX hnβ
  have hA : ∀ g : X, g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} →
      g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z := by
    intro k hk
    rcases hc.conj_t_X_cases hk with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      apply hc.conj_t_ne_z₁ (g₁ * k)
      calc g₁ * k * t * (g₁ * k)⁻¹ = g₁ * (k * t * k⁻¹) * g₁⁻¹ := by group
        _ = g₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g₁⁻¹ := by rw [h1]
        _ = z₁ := hg₁
    · exact Or.inr h1
    · exfalso
      apply hc.conj_t_ne_z₁ (g₁ * z₁⁻¹ * k)
      calc g₁ * z₁⁻¹ * k * t * (g₁ * z₁⁻¹ * k)⁻¹ =
          g₁ * (z₁⁻¹ * (k * t * k⁻¹) * z₁) * g₁⁻¹ := by group
        _ = g₁ * (z₁⁻¹ * (z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹) * z₁) *
            g₁⁻¹ := by rw [h1, hc.z₁_conj_t_mul]
        _ = g₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g₁⁻¹ := by group
        _ = z₁ := hg₁
  refine ⟨hA, ⟨g₁, hg₁⟩, ?_⟩
  have h1 := L415.twoPart_centralizer_conj (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) g₁
  rw [hg₁] at h1
  have hW₀ := hc.card_W₀
  have h2 : Nat.card ↥(W ⊓ centralizer ({z₁} : Set X)) ≤ twoPart (centralizer ({z₁} : Set X)) :=
    card_le_twoPart (hc.isSylowOf_W.isPGroup.to_le inf_le_left) inf_le_right
  have h3 := hc.card_le
  have hTpos : 0 < Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) := Nat.card_pos
  have h4 : Nat.card ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) ≤
      twoPart (centralizer ({z₁} : Set X)) :=
    card_le_twoPart (h𝒱.isPGroup.to_le inf_le_left) inf_le_right
  have h5 : Nat.card 𝒱 = 2 * Nat.card ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) := by
    have h6 := Subgroup.relIndex_mul_card (𝒱 ⊓ centralizer ({z₁} : Set X)) 𝒱
    rw [inf_of_le_left inf_le_left, hc.relIndex_V₀ hW𝒱 hstar hz𝒱] at h6
    exact h6.symm
  have h6 : twoPart (⊤ : Subgroup X) = Nat.card 𝒱 := h𝒱.card_eq.symm
  have hβ' := hσ.isBeta411_t_mul hKF hKC hs.sylow_V hs.le_V hs.beta.mem_X hs.beta.not_mem hA
    (by omega) (by omega)
  have h7 := hs.max_beta _ hβ'
  omega

end Config415

end CFSG.ComponentClassification.HarrisLit
