module

public import CFSG.ClassicalInvolution.Phan.PhanB10Family

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section GlueLeft

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem exists_glue_left (hK : Nat.card K = (p ^ f) ^ 2) {θ₁ θ₂ : Su K p f 3 →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (Su K p f 3)) (h₂ : θ₂.ker ≤ Subgroup.center (Su K p f 3))
    (hM : (B23 K p f).map θ₁ = (B12 K p f).map θ₂)
    (hcomm : ∀ x ∈ (B12 K p f).map θ₁, ∀ y ∈ (B23 K p f).map θ₂, x * y = y * x) :
    ∃ θ : Su K p f 3 →* X, θ.ker ≤ Subgroup.center (Su K p f 3) ∧ θ.range = θ₁.range ∧
      (B12 K p f).map θ = (B12 K p f).map θ₁ ∧ (B23 K p f).map θ = (B23 K p f).map θ₁ ∧
      θ.comp (embSUid (unitaryInvolution K p f) 0) =
        θ₂.comp (embSUid (unitaryInvolution K p f) 2) := by
  have ha₁ : Function.Injective (θ₂.comp (embSUid (unitaryInvolution K p f) 2)) :=
    comp_embSUid_injective hK h₂ 2
  have ha₂ : Function.Injective (θ₁.comp (embSUid (unitaryInvolution K p f) 0)) :=
    comp_embSUid_injective hK h₁ 0
  have hr : (θ₂.comp (embSUid (unitaryInvolution K p f) 2)).range =
      (θ₁.comp (embSUid (unitaryInvolution K p f) 0)).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp]
    exact hM.symm
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq ha₁ ha₂ hr
  have htor : (diagTorus2 K p f).map α.toMonoidHom = diagTorus2 K p f := by
    have hτ := torus_agree hK h₁ h₂ hM hcomm
    rw [map_D23, map_D12] at hτ
    have e : θ₂.comp (embSUid (unitaryInvolution K p f) 2) =
        (θ₁.comp (embSUid (unitaryInvolution K p f) 0)).comp α.toMonoidHom :=
      MonoidHom.ext fun A => (hα A).symm
    rw [e] at hτ
    conv_rhs at hτ => rw [← Subgroup.map_map]
    exact (Subgroup.map_injective ha₂ hτ).symm
  obtain ⟨β, hβ0, hβ12, hβ23⟩ := PhanB3.exists_mulAut_extend_zero hK α htor.le
  refine ⟨θ₁.comp β.toMonoidHom, ker_comp_mulEquiv_le_center h₁ β, range_comp_mulEquiv θ₁ β,
    ?_, ?_, MonoidHom.ext fun A => ?_⟩
  · rw [map_comp_mulEquiv, hβ12]
  · rw [map_comp_mulEquiv, hβ23]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ0]
    exact hα A

end GlueLeft

end CFSG.ClassicalInvolution.Phan
