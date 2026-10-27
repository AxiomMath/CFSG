module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

section Ambient

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

@[expose] def restrictInvolution {Y : Type*} [Group Y] (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (Q : Subgroup Y) (hQ : ∀ y ∈ Q, σ y ∈ Q) : Q ≃* Q :=
  (σ.subgroupMap Q).trans (MulEquiv.subgroupCongr (le_antisymm
    (by rintro _ ⟨y, hy, rfl⟩; exact hQ y hy)
    (fun y hy => ⟨σ y, hQ y hy, hσ y⟩)))

theorem coe_restrictInvolution {Y : Type*} [Group Y] (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (Q : Subgroup Y) (hQ : ∀ y ∈ Q, σ y ∈ Q) (x : Q) :
    ((restrictInvolution σ hσ Q hQ x : Q) : Y) = σ x :=
  rfl

theorem unitaryAutClassification_ambient (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {d : ℕ} (hd : 3 ≤ d) {Y : Type} [Group Y] (θ : Su K p f d →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f d)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) :
    ∃ (α : Su K p f d →* Su K p f d) (g : GL (Fin d) K) (φ : K ≃+* K),
      (∀ x, θ (α x) = σ (θ x)) ∧
      (∀ x, ((α x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) *
          φ.mapMatrix ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      ((g : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin d) (Fin d) K) = 1 ∧
      (φ = RingEquiv.refl K ∨ φ = unitaryInvolution K p f) ∧ α.comp α = MonoidHom.id _ := by
  have hQ : ∀ y ∈ θ.range, σ y ∈ θ.range := by
    rintro _ ⟨x, rfl⟩
    exact hstab x
  have hσ' : ∀ y, restrictInvolution σ hσ θ.range hQ (restrictInvolution σ hσ θ.range hQ y) =
      y := fun y => Subtype.ext (by simp only [coe_restrictInvolution]; exact hσ _)
  obtain ⟨α, g, φ, h1, h2, h3, h4⟩ := unitaryAutClassification_isometry_of_card hK hp2 hq hd
    θ.range θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictInvolution σ hσ θ.range hQ)
  obtain ⟨h5, h6⟩ := h4 hσ'
  exact ⟨α, g, φ, fun x => congrArg Subtype.val (h1 x), h2, h3, h5, h6⟩

end Ambient

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
