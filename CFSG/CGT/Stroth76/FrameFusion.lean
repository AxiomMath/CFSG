module

public import CFSG.CGT.Stroth76.Lemma4
public import CFSG.CGT.Stroth76.MnsFusion
public import CFSG.CGT.Stroth76.NoInvFrame

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

theorem mnsX1_mul_mnsX_inv : (mnsX1 * mnsX)⁻¹ = mnsX := by decide
theorem mnsY1_mul_mnsY_inv : (mnsY1 * mnsY)⁻¹ = mnsY := by decide

variable {G : Type*} [Group G] [Finite G]

theorem arch76_fusion_of_model_of_eq (K : Config G) {E₀ : Subgroup G}
    (hE₀ : E₀ = Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t})
    (φ : ↥(Subgroup.normalizer (E₀ : Set G)) →* Mns) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.oddCore _)
    (hφw : ∀ h, φ ⟨K.w, h⟩ = mnsW) (hφx : ∀ h, φ ⟨K.x, h⟩ = mnsX)
    (hφy : ∀ h, φ ⟨K.y, h⟩ = mnsY) (hφuv : ∀ h, φ ⟨K.uv, h⟩ = mnsUV)
    (hφt : ∀ h, φ ⟨K.t, h⟩ = mnsT) (hφu : ∀ h, φ ⟨K.u, h⟩ = mnsU) :
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2)) ∧
    IsConj K.u K.w ∧ IsConj (K.w * K.u) (K.x * K.y * K.uv) ∧
    (∀ g ∈ Subgroup.closure {K.x, K.y, K.uv, K.t, K.w * K.u}, orderOf g = 2 →
      IsConj g ((K.x * K.y) ^ 2) ∨ IsConj g (K.x * K.y * K.uv)) ∧
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, orderOf (K.w * e) = 2 →
      IsConj (K.w * e) K.w) ∧
    (∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, orderOf (K.x * K.y * e) = 2 →
      IsConj (K.x * K.y * e) (K.x * K.y * K.uv)) := by
  subst hE₀
  exact arch76_fusion_of_model K φ hφ hker (hφw _) (hφx _) (hφy _) (hφuv _) (hφt _) (hφu _)

section Frame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_fusion :
    (∀ e ∈ Subgroup.closure {F.dA.toConfig.x ^ 2, F.dA.toConfig.y ^ 2, F.dA.toConfig.uv,
        F.dA.toConfig.t}, e ≠ 1 →
      IsConj e ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) ∧
    IsConj F.dA.toConfig.u F.dA.toConfig.w ∧
    IsConj (F.dA.toConfig.w * F.dA.toConfig.u)
      (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.toConfig.uv) ∧
    (∀ g ∈ Subgroup.closure {F.dA.toConfig.x, F.dA.toConfig.y, F.dA.toConfig.uv,
        F.dA.toConfig.t, F.dA.toConfig.w * F.dA.toConfig.u}, orderOf g = 2 →
      IsConj g ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) ∨
        IsConj g (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.toConfig.uv)) ∧
    (∀ e ∈ Subgroup.closure {F.dA.toConfig.x ^ 2, F.dA.toConfig.y ^ 2, F.dA.toConfig.uv,
        F.dA.toConfig.t}, orderOf (F.dA.toConfig.w * e) = 2 →
      IsConj (F.dA.toConfig.w * e) F.dA.toConfig.w) ∧
    (∀ e ∈ Subgroup.closure {F.dA.toConfig.x ^ 2, F.dA.toConfig.y ^ 2, F.dA.toConfig.uv,
        F.dA.toConfig.t}, orderOf (F.dA.toConfig.x * F.dA.toConfig.y * e) = 2 →
      IsConj (F.dA.toConfig.x * F.dA.toConfig.y * e)
        (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.toConfig.uv)) := by
  obtain ⟨φ, hφ, hker, huv, ht, hu, -, hw, ha, hb⟩ := F.model
  refine arch76_fusion_of_model_of_eq F.dA.toConfig (frame_closureE_eq F).symm φ hφ hker
    (fun _ => hw) (fun h => ?_) (fun h => ?_) (fun _ => huv) (fun _ => ht) (fun _ => hu)
  · have : (⟨F.dA.toConfig.x, h⟩ : ↥(Subgroup.normalizer (F.E : Set G))) =
        (⟨(F.dA.a : G), F.A_le F.dA.a.2⟩)⁻¹ := rfl
    rw [this, map_inv, ha, mnsX1_mul_mnsX_inv]
  · have : (⟨F.dA.toConfig.y, h⟩ : ↥(Subgroup.normalizer (F.E : Set G))) =
        (⟨(F.dA.b : G), F.A_le F.dA.b.2⟩)⁻¹ := rfl
    rw [this, map_inv, hb, mnsY1_mul_mnsY_inv]

include F in
theorem frame_nonab : ∃ a b : G, a * b ≠ b * a := by
  refine ⟨F.dA.toConfig.uv, F.dA.toConfig.x, fun h => ?_⟩
  have h1 := F.dA.toConfig.huv_x
  have h2 : F.dA.toConfig.uv⁻¹ * F.dA.toConfig.x * F.dA.toConfig.uv = F.dA.toConfig.x := by
    rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h2] at h1
  have h3 : F.dA.toConfig.y ^ 2 = 1 := by
    have := congrArg (fun z => F.dA.toConfig.x⁻¹ * z) h1
    simpa using this.symm
  have hne : F.dA.toConfig.ev (0, 0, 2) ≠ F.dA.toConfig.ev 0 :=
    fun he => absurd (F.dA.toConfig.ev_injective he) (by decide)
  apply hne
  simpa [Config.ev, show (2 : ZMod 4).val = 2 from rfl] using h3

theorem frame_arch76Lemma4
    (hAnn1 : ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2))
    (S : Sylow 2 G) (hTS : F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤ S) :
    F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≠ S := by
  haveI := F.simple
  obtain ⟨hfusE, -, -, hfusW, -, -⟩ := frame_fusion F
  exact arch76Lemma4 F.dA.toConfig (frame_nonab F) (Or.inr rfl) hfusE hfusW hAnn1 S hTS

end Frame

end CFSG.CGT.Stroth76
