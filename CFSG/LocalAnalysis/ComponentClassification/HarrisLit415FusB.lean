module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415FusA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Z2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem conj_mem_of_map_conj {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = B) {y : G} (hy : y ∈ B) : g⁻¹ * y * g ∈ A := by
  rw [← h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [MulAut.conj_apply, mul_assoc] using hx

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem conj_z_ne_t_mul_beta (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) (g : X) :
    g * z * g⁻¹ ≠ t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have hσ := hs.setup
  intro h1
  have hfus : ∀ k : X, k * t * k⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} →
      k * t * k⁻¹ = t ∨ k * t * k⁻¹ = t * z := by
    intro k hk
    rcases hc.conj_t_X_cases hk with h2 | h2 | h2 | h2
    · exact Or.inl h2
    · exfalso
      apply hσ.conj_t_ne_z (g⁻¹ * k)
      calc g⁻¹ * k * t * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * t * k⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h2, h1]
        _ = z := by group
    · exact Or.inr h2
    · exfalso
      apply hσ.conj_t_ne_z (g⁻¹ * z₁⁻¹ * k)
      calc g⁻¹ * z₁⁻¹ * k * t * (g⁻¹ * z₁⁻¹ * k)⁻¹ =
          g⁻¹ * (z₁⁻¹ * (k * t * k⁻¹) * z₁) * g := by group
        _ = g⁻¹ * (z₁⁻¹ * (z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹) * z₁) * g := by
          rw [h2, hc.z₁_conj_t_mul]
        _ = g⁻¹ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
        _ = z := by group
  have h2 := L415.twoPart_centralizer_conj z g
  rw [h1] at h2
  have h3 := L415.card_le_twoPart_of_comm h𝒱.isPGroup hz𝒱
  have h4 := hc.card_W_lt_V hW𝒱 hcen
  have h5 : twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) =
      Nat.card W := hc.isSylowOf_W.card_eq.symm
  have h6 : twoPart (⊤ : Subgroup X) = Nat.card 𝒱 := h𝒱.card_eq.symm
  have h7 := hc.card_le
  have hTpos : 0 < Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) := Nat.card_pos
  have hβ' := hσ.isBeta411_t_mul hKF hKC hs.sylow_V hs.le_V hs.beta.mem_X hs.beta.not_mem hfus
    (by omega) (by omega)
  have h8 := hs.max_beta _ hβ'
  omega

theorem eq_z_of_conj_X (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X}
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) {g : X}
    (hg : g * z * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) : g * z * g⁻¹ = z := by
  have hσ := hs.setup
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  rcases hc.mem_X_cases hg with h1 | h1
  · rcases hc.mem_beta_z_cases h1 with h2 | h2 | h2 | h2
    · exfalso
      apply hσ.z_ne_one
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · exact absurd h2 (hc.conj_z_ne_beta h𝒱 hW𝒱 hcen hz𝒱 g)
    · exact h2
    · exfalso
      apply hc.conj_z_ne_beta h𝒱 hW𝒱 hcen hz𝒱 (τ⁻¹ * g)
      calc τ⁻¹ * g * z * (τ⁻¹ * g)⁻¹ = τ⁻¹ * (g * z * g⁻¹) * τ := by group
        _ = τ⁻¹ * (τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹) * τ := by rw [h2, hτβ]
        _ = w ^ (orderOf w / 2) * t ^ i * z ^ j := by group
  · have h2 : g * z * g⁻¹ = t * (t * (g * z * g⁻¹)) := by rw [← mul_assoc t t, ht2, one_mul]
    rcases hc.mem_beta_z_cases h1 with h3 | h3 | h3 | h3 <;> rw [h3] at h2
    · exfalso
      apply hσ.conj_t_ne_z g⁻¹
      calc g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h2, mul_one, inv_inv]
        _ = z := by group
    · exact absurd h2 (hc.conj_z_ne_t_mul_beta hKF hKC h𝒱 hW𝒱 hcen hz𝒱 g)
    · exfalso
      apply hσ.conj_t_ne_z (g⁻¹ * z₁)
      calc g⁻¹ * z₁ * t * (g⁻¹ * z₁)⁻¹ = g⁻¹ * (z₁ * t * z₁⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hc.z₁_conj_t, h2]
        _ = z := by group
    · exfalso
      apply hc.conj_z_ne_t_mul_beta hKF hKC h𝒱 hW𝒱 hcen hz𝒱 (z₁⁻¹ * g)
      calc z₁⁻¹ * g * z * (z₁⁻¹ * g)⁻¹ = z₁⁻¹ * (g * z * g⁻¹) * z₁ := by group
        _ = z₁⁻¹ * (z₁ * (t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * z₁⁻¹) * z₁ := by
          rw [h2, hc.z₁_conj_t_mul]
        _ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by group

theorem not_conj_z_of (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X}
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) {α g₀ : X}
    (hX : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g₀).toMonoidHom =
      closure {α, z₁, t * z₁ * t⁻¹}) (h : X) : h * z₁ * h⁻¹ ≠ z := by
  intro h1
  have hz₁Y : z₁ ∈ closure ({α, z₁, t * z₁ * t⁻¹} : Set X) := subset_closure (by simp)
  have hzY : z ∈ closure ({α, z₁, t * z₁ * t⁻¹} : Set X) := by
    rw [hc.z_eq]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hz₁' : h⁻¹ * z * h = z₁ := by rw [← h1]; group
  have h2 : g₀⁻¹ * z * g₀⁻¹⁻¹ = z := hc.eq_z_of_conj_X hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ (by
    rw [inv_inv]
    exact L415.conj_mem_of_map_conj hX hzY)
  have h3 : (g₀⁻¹ * h⁻¹) * z * (g₀⁻¹ * h⁻¹)⁻¹ = z :=
    hc.eq_z_of_conj_X hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ (by
      rw [show (g₀⁻¹ * h⁻¹) * z * (g₀⁻¹ * h⁻¹)⁻¹ = g₀⁻¹ * (h⁻¹ * z * h) * g₀ by group, hz₁']
      exact L415.conj_mem_of_map_conj hX hz₁Y)
  have h4 : z₁ = z := by
    have h5 : g₀⁻¹ * z₁ * g₀ = g₀⁻¹ * z * g₀ := by
      rw [← hz₁']
      calc g₀⁻¹ * (h⁻¹ * z * h) * g₀ = (g₀⁻¹ * h⁻¹) * z * (g₀⁻¹ * h⁻¹)⁻¹ := by group
        _ = z := h3
        _ = g₀⁻¹ * z * g₀⁻¹⁻¹ := h2.symm
        _ = g₀⁻¹ * z * g₀ := by rw [inv_inv]
    exact mul_left_cancel (mul_right_cancel h5)
  have h6 : t * z₁ * t⁻¹ = 1 := by
    have h7 : z₁ * (t * z₁ * t⁻¹) = z₁ * 1 := by rw [mul_one, ← hc.z_eq, h4]
    exact mul_left_cancel h7
  apply hc.z₁_ne
  rw [h6]
  calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
    _ = 1 := by rw [h6]; group

theorem isSylowOf_V₀ (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hcen : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X}
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) {α g₀ : X}
    (hX : (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g₀).toMonoidHom =
      closure {α, z₁, t * z₁ * t⁻¹})
    (hstar : ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹) :
    IsSylowOf 2 (𝒱 ⊓ centralizer {z₁}) (centralizer {z₁}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hV₀P⟩ := exists_isSylowOf_ge (h𝒱.isPGroup.to_le inf_le_left)
    (inf_le_right : 𝒱 ⊓ centralizer ({z₁} : Set X) ≤ centralizer {z₁})
  by_cases hEq : P = 𝒱 ⊓ centralizer {z₁}
  · rwa [hEq] at hP
  exfalso
  have h2 := two_mul_card_le_of_lt (lt_of_le_of_ne hV₀P (Ne.symm hEq))
  have h3 : Nat.card 𝒱 = 2 * Nat.card ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) := by
    have h4 := Subgroup.relIndex_mul_card (𝒱 ⊓ centralizer ({z₁} : Set X)) 𝒱
    rw [inf_of_le_left inf_le_left, hc.relIndex_V₀ hW𝒱 hstar hz𝒱] at h4
    exact h4.symm
  have h5 : Nat.card P ≤ Nat.card 𝒱 := by
    rw [h𝒱.card_eq]
    exact card_le_twoPart hP.isPGroup le_top
  have hPsyl : IsSylowOf 2 P ⊤ := isSylowOf_of_card le_top (by rw [← h𝒱.card_eq]; omega)
  obtain ⟨k, -, hk⟩ := h𝒱.exists_mem_conj hPsyl
  have hz₁P : z₁ ∈ P :=
    hV₀P (mem_inf.mpr ⟨hW𝒱 hc.z₁_mem, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hc1 : k⁻¹ * z₁ * k ∈ 𝒱 := (hk z₁).mp hz₁P
  have hc2 : ∀ v ∈ 𝒱, (k⁻¹ * z₁ * k) * v = v * (k⁻¹ * z₁ * k) := by
    intro v hv
    have hv' : k * v * k⁻¹ ∈ P := (hk _).mpr (by
      rw [show k⁻¹ * (k * v * k⁻¹) * k = v by group]
      exact hv)
    have h6 : k * v * k⁻¹ * z₁ = z₁ * (k * v * k⁻¹) :=
      mem_centralizer_singleton_iff.mp (hP.le hv')
    calc k⁻¹ * z₁ * k * v = k⁻¹ * (z₁ * (k * v * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * v * k⁻¹ * z₁) * k := by rw [h6]
      _ = v * (k⁻¹ * z₁ * k) := by group
  rcases hcen _ hc1 hc2 with h7 | h7
  · apply hc.z₁_ne
    have h8 : z₁ = 1 := by
      calc z₁ = k * (k⁻¹ * z₁ * k) * k⁻¹ := by group
        _ = 1 := by rw [h7]; group
    rw [h8]
    group
  · exact hc.not_conj_z_of hKF hKC h𝒱 hW𝒱 hcen hz𝒱 hτβ hX k⁻¹ (by rw [inv_inv]; exact h7)

end Config415

end CFSG.ComponentClassification.HarrisLit
