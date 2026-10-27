module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitHigh

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {W : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) 2 W) {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 W ψ Φ)
  {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀) {X₂ : Subgroup G} (hX₂U : X₂ ≤ U ⊔ zpowers ρ)
  (hX₂E : ∀ k ∈ X₂, k ∈ Q ⊔ zpowers t → k = 1)
include hS hC hΦ hρ hX₂U hX₂E

omit hC in
theorem eq_of_rep_X₂ [Finite G] {k k' : G} (hk : k ∈ X₂) (hk' : k' ∈ X₂)
    {F : Matrix (Fin 6) (Fin 6) (ZMod 4)} (h1 : Rep Φ k F) (h2 : Rep Φ k' F) : k = k' := by
  have hR := hS.rad
  have hr : k⁻¹ * k' ∈ X₂ := mul_mem (inv_mem hk) hk'
  have hr1 : Rep Φ (k⁻¹ * k') 1 := fun v => by
    rw [one_mulVec]
    calc k⁻¹ * k' * Φ v * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * Φ v * k'⁻¹) * k := by group
      _ = k⁻¹ * Φ (F *ᵥ v) * k := by rw [h2]
      _ = k⁻¹ * (k * Φ v * k⁻¹) * k := by rw [h1]
      _ = Φ v := by group
  have hrQ : k⁻¹ * k' ∈ Q := by
    refine mem_Q_of_Urho hS hρ (hX₂U hr) fun q hq => ?_
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have := hΦ.conj_ψ_of_rep hr1 v
    rw [Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this
    calc k⁻¹ * k' * ψ v = k⁻¹ * k' * ψ v * (k⁻¹ * k')⁻¹ * (k⁻¹ * k') := by group
      _ = ψ v * (k⁻¹ * k') := by rw [this]
  have := hX₂E _ hr (mem_sup_left hrQ)
  calc k = k * (k⁻¹ * k') := by rw [this, mul_one]
    _ = k' := by group

omit hX₂E in
theorem exists_rep_X₂ [Finite G]
    (hreal : ∀ j < 128, ∃ y ∈ U ⊔ zpowers ρ, Rep Φ y (toMat4 (tilGet ε j)))
    (hdec : ∀ y ∈ U ⊔ zpowers x₀ ⊔ zpowers t, ∃ q ∈ Q, ∃ k ∈ X₂, y = q * k ∨ y = q * k * t)
    {j : ℕ} (hj : j < 128) : ∃ k ∈ X₂, Rep Φ k (toMat4 (tilGet ε j)) := by
  obtain ⟨y, hy, hyj⟩ := hreal j hj
  obtain ⟨q, hq, k, hk, hyk | hyk⟩ := hdec y (hS.Urho_le_TH hρ hy)
  · refine ⟨k, hk, fun v => ?_⟩
    have hq1 := hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hq)
    have h1 := hyj v
    rw [hyk] at h1
    have h2 := hq1 (toMat4 (tilGet ε j) *ᵥ v)
    rw [one_mulVec] at h2
    calc k * Φ v * k⁻¹ = q⁻¹ * (q * k * Φ v * (q * k)⁻¹) * q := by group
      _ = q⁻¹ * Φ (toMat4 (tilGet ε j) *ᵥ v) * q := by rw [h1]
      _ = Φ (toMat4 (tilGet ε j) *ᵥ v) := by
        calc q⁻¹ * Φ (toMat4 (tilGet ε j) *ᵥ v) * q =
            q⁻¹ * (q * Φ (toMat4 (tilGet ε j) *ᵥ v) * q⁻¹) * q := by rw [h2]
          _ = _ := by group
  · exfalso
    apply hS.t_not_mem_Urho hρ
    have : t = (q * k)⁻¹ * y := by rw [hyk]; group
    rw [this]
    exact mul_mem (inv_mem (mul_mem (mem_sup_left (hS.rad.Q_le_U hq)) (hX₂U hk))) hy

omit hS hC hρ hX₂U hX₂E in
theorem test_of_commX {m h₀ : G} {F M : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hm : Rep Φ m F)
    (hh₀ : Rep Φ h₀ M) (hmh : m * h₀ * m⁻¹ = h₀) {w x : Fin 6 → ZMod 4}
    (hc : Φ w * m * (Φ x * h₀) = Φ x * h₀ * (Φ w * m)) :
    (1 - M) *ᵥ w = (1 - F) *ᵥ x := by
  have e1 : Φ w * m * (Φ x * h₀) * (Φ w * m)⁻¹ =
      Φ w * (m * Φ x * m⁻¹) * (m * h₀ * m⁻¹) * (Φ w)⁻¹ := by group
  have e2 : Φ x * h₀ = Φ w * m * (Φ x * h₀) * (Φ w * m)⁻¹ := by rw [hc]; group
  rw [e1, hm, hmh] at e2
  have e3 : Φ w * Φ (F *ᵥ x) * h₀ * (Φ w)⁻¹ = Φ (w + F *ᵥ x - M *ᵥ w) * h₀ := by
    rw [sub_eq_add_neg, hΦ.add, hΦ.add, hΦ.neg]
    have := hh₀ w
    calc Φ w * Φ (F *ᵥ x) * h₀ * (Φ w)⁻¹ = Φ w * Φ (F *ᵥ x) * (h₀ * Φ w * h₀⁻¹)⁻¹ * h₀ := by
          group
      _ = _ := by rw [this]
  rw [e3] at e2
  have e4 : x = w + F *ᵥ x - M *ᵥ w := hΦ.injective (mul_right_cancel e2)
  rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec]
  calc w - M *ᵥ w = (w + F *ᵥ x - M *ᵥ w) - F *ᵥ x := by abel
    _ = x - F *ᵥ x := by rw [← e4]

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
