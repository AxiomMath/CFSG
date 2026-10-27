module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Sylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Rank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup
open scoped commutatorElement

theorem finrank_range_sub_one_congr {W U : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U] (τ : W ≃ₗ[ZMod 2] U) (f : W →ₗ[ZMod 2] W)
    (g : U →ₗ[ZMod 2] U) (h : ∀ v, τ (f v) = g (τ v)) :
    Module.finrank (ZMod 2) (LinearMap.range (g - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (f - 1)) := by
  have : LinearMap.range (g - 1) = (LinearMap.range (f - 1)).map (τ : W →ₗ[ZMod 2] U) := by
    ext u
    constructor
    · rintro ⟨u', rfl⟩
      refine ⟨(f - 1) (τ.symm u'), ⟨τ.symm u', rfl⟩, ?_⟩
      simp [h]
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨τ v, ?_⟩
      simp [h]
  rw [this]
  exact (LinearEquiv.finrank_map_eq τ _)

theorem rank_bounds {Q W : Type} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hQ : IsPGroup 5 Q) (σ : Q →* (W ≃ₗ[ZMod 2] W))
    (hσ : Function.Injective σ) (hn : Module.finrank (ZMod 2) W = 20)
    (J : Subgroup Q) (hJc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) (hJcard : Nat.card J = 5 ^ 4)
    (hQcard : Nat.card Q ≤ 5 ^ 5) (hQnc : ∃ a b : Q, a * b ≠ b * a) :
    (∀ g : Q, g ∉ J →
      16 ≤ Module.finrank (ZMod 2) (LinearMap.range ((σ g : W →ₗ[ZMod 2] W) - 1))) ∧
    (∀ q : Q, ∀ j ∈ J, q * j * q⁻¹ ∈ J) ∧
    (∀ e ∈ ⁅J, (⊤ : Subgroup Q)⁆, e ≠ 1 →
      12 ≤ Module.finrank (ZMod 2) (LinearMap.range ((σ e : W →ₗ[ZMod 2] W) - 1))) := by
  obtain ⟨τ, ψ, hψ, hτψ⟩ := exists_model_embedding hQ σ hσ hn
  have hrank : ∀ g : Q, Module.finrank (ZMod 2) (LinearMap.range (T (ψ g) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range ((σ g : W →ₗ[ZMod 2] W) - 1)) := fun g =>
    finrank_range_sub_one_congr τ (σ g : W →ₗ[ZMod 2] W) (T (ψ g)) (fun v => hτψ g v)
  have hMcard : Nat.card ψ.range ≤ 5 ^ 5 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
    exact hQcard
  have hJMcard : Nat.card (J.map ψ) = 5 ^ 4 := by
    rw [Subgroup.card_map_of_injective hψ, hJcard]
  have hJMc : ∀ j ∈ J.map ψ, ∀ k ∈ J.map ψ, j * k = k * j := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hJc a ha b hb]
  have hMc : ∃ w ∈ ψ.range, w.c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hQnc
    apply hab
    apply hψ
    rw [map_mul, map_mul]
    have ha := hcon (ψ a) ⟨a, rfl⟩
    have hb := hcon (ψ b) ⟨b, rfl⟩
    refine Wr.ext (funext fun i => ?_) (by simp [ha, hb])
    simp only [Wr.mul_a, ha, hb, sub_zero]
    ring
  obtain ⟨h1, hn, h2⟩ := rank_bounds_model ψ.range (J.map ψ) (Subgroup.map_le_range ψ J) hJMc
    hJMcard hMcard hMc
  refine ⟨fun g hg => ?_, fun q j hj => ?_, fun e he he1 => ?_⟩
  · rw [← hrank]
    refine rank_ge_sixteen (h1 (ψ g) ⟨g, rfl⟩ ?_)
    rintro ⟨x, hx, hxg⟩
    exact hg (hψ hxg ▸ hx)
  · have h3 := hn (ψ q) ⟨q, rfl⟩ (ψ j) ⟨j, hj, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at h3
    obtain ⟨x, hx, hxq⟩ := h3
    have : x = q * j * q⁻¹ := hψ hxq
    rwa [this] at hx
  · rw [← hrank]
    have he' : ψ e ∈ ⁅J.map ψ, ψ.range⁆ := by
      rw [← Subgroup.map_top ψ, ← Subgroup.map_commutator]
      exact ⟨e, he, rfl⟩
    have hne : ψ e ≠ 1 := fun h => he1 (hψ (by rw [h, map_one]))
    obtain ⟨hc, hz⟩ := h2 (ψ e) he' hne
    exact rank_ge_twelve hc hz

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
