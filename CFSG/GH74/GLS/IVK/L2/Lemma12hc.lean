module

public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.FieldProj

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem ivk_1_2h_c : IVK_1_2h_c := by
  intro F _ _ hF K _ _ e N f hf hf2 x hx hx2
  obtain ⟨σ, hσ⟩ : f ∈ fieldAutSub e := hf.2
  obtain ⟨g, hg⟩ : x ∈ innDiagSub e := hx
  have hΘf : thetaAut e f = SemidirectProduct.inr σ := by
    rw [← hσ]
    exact thetaAut_fieldAutHom e σ
  have hΘx : thetaAut e x = SemidirectProduct.inl g := by
    rw [← hg]
    exact thetaAut_innDiagHom e g
  have hΘy : thetaAut e (x * f) = SemidirectProduct.inl g * SemidirectProduct.inr σ := by
    rw [map_mul, hΘx, hΘf]
  have hright : (thetaAut e (x * f)).right = σ := by
    rw [hΘy]
    simp
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have : f = 1 := by rw [← hσ]; exact map_one _
    rw [this, orderOf_one] at hf2
    omega
  have hord : orderOf (thetaAut e (x * f)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e (x * f)) hord
    (by rw [hright]; exact hσ1)
  rw [hright] at hC
  refine ⟨innDiagHom e C⁻¹, ⟨C⁻¹, rfl⟩, ?_⟩
  have hΘa : thetaAut e (innDiagHom e C⁻¹) = (SemidirectProduct.inl C)⁻¹ := by
    rw [thetaAut_innDiagHom, map_inv]
  apply (thetaAut e).injective
  rw [map_mul, map_mul, map_inv (thetaAut e), hΘa, inv_inv, hΘf]
  exact hC

end CFSG.GH74.GLS.IVK
