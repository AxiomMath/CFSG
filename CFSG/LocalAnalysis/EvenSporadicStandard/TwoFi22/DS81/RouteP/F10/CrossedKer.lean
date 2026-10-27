module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Kernel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {Q W B : Type*} [Group Q] [CommGroup W] [Group B] {ρ : Q →* MulAut W}
  (X : ExtData ρ B)

theorem exists_principal_of_crossedHom (hH1 : ModH1Trivial ρ) (F : B → ↥X.π.ker)
    (hF : ∀ b₁ b₂ : B, ((F (b₁ * b₂) : ↥X.π.ker) : B) =
      (F b₁ : B) * (b₁ * (F b₂ : B) * b₁⁻¹))
    (hFE : ∀ b ∈ X.π.ker, F b = 1) :
    ∃ e : ↥X.π.ker, ∀ b : B, ((F b : ↥X.π.ker) : B) = (e : B) * (b * (e : B)⁻¹ * b⁻¹) := by
  classical
  have hconst : ∀ b c : B, X.π b = X.π c → F b = F c := by
    intro b c hbc
    have hx : X.π (b⁻¹ * c) = 1 := by rw [map_mul, map_inv, hbc, inv_mul_cancel]
    have h1 : (F (b⁻¹ * c) : B) = 1 := by
      rw [hFE (b⁻¹ * c) hx, Subgroup.coe_one]
    have h := hF b (b⁻¹ * c)
    rw [h1, mul_one, mul_inv_cancel, mul_one] at h
    have hb : b * (b⁻¹ * c) = c := by group
    rw [hb] at h
    exact (Subtype.ext h).symm
  let s : Q → B := Function.surjInv X.π_surjective
  have hs : ∀ q, X.π (s q) = q := Function.surjInv_eq X.π_surjective
  let f : Q → W := fun q => X.eT (F (s q))
  have hf_pi : ∀ b : B, f (X.π b) = X.eT (F b) := by
    intro b
    show X.eT (F (s (X.π b))) = X.eT (F b)
    rw [hconst (s (X.π b)) b (hs (X.π b))]
  have hf_crossed : ∀ q₁ q₂ : Q, f (q₁ * q₂) = f q₁ * ρ q₁ (f q₂) := by
    intro q₁ q₂
    have hq1 : X.π (s q₁) = q₁ := hs q₁
    have hq2 : X.π (s q₂) = q₂ := hs q₂
    have hq : q₁ * q₂ = X.π (s q₁ * s q₂) := by rw [map_mul, hq1, hq2]
    rw [hq, hf_pi]
    have hFmul : F (s q₁ * s q₂) =
        F (s q₁) * MulAut.conjNormal (s q₁) (F (s q₂)) :=
      Subtype.ext (hF (s q₁) (s q₂))
    rw [hFmul]
    change X.kerEquiv (F (s q₁) * MulAut.conjNormal (s q₁) (F (s q₂))) =
      f q₁ * ρ q₁ (f q₂)
    rw [map_mul, X.kerEquiv_conj, hq1]
    rfl
  obtain ⟨w, hw⟩ := hH1 f hf_crossed
  obtain ⟨x, hxker, hxw⟩ := X.eT_surj w
  refine ⟨⟨x, hxker⟩, fun b => ?_⟩
  have hxeq : X.kerEquiv ⟨x, hxker⟩ = w := by
    rw [X.kerEquiv_apply]
    exact hxw
  have key : X.kerEquiv (F b) =
      X.kerEquiv (⟨x, hxker⟩ * (MulAut.conjNormal b ⟨x, hxker⟩)⁻¹) := by
    rw [map_mul, map_inv, X.kerEquiv_conj]
    change X.eT (F b) = X.kerEquiv ⟨x, hxker⟩ *
      (ρ (X.π b) (X.kerEquiv ⟨x, hxker⟩))⁻¹
    rw [← hf_pi b, hxeq]
    rw [hw]
  have hFb : F b = ⟨x, hxker⟩ * (MulAut.conjNormal b ⟨x, hxker⟩)⁻¹ :=
    X.kerEquiv.injective key
  rw [hFb, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
  group

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
