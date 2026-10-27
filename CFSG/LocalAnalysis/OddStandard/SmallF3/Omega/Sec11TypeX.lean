module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXFus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11InputsT

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Certificates.OmegaInv Certificates.OmegaT11

variable {G : Type} [Group G]

private theorem t11x_conjugate_inv (L : Subgroup G) (h : G) :
    CFSG.conjugate (CFSG.conjugate L h) h⁻¹ = L := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, show h * (h⁻¹ * x * h⁻¹⁻¹) * h⁻¹ = x by group]

theorem asc82Step1110Type_of
    (hp : Asc82Pre11) : Asc82Step1110Type := by
  intro G _ _ t L S z K1 K2 T R hctx h hh hsS hty
  have H : T11Hyp t L S z K1 K2 T R h := ⟨hp, hctx, hh, hsS, hty⟩
  obtain ⟨F, hsN, hF⟩ :=
    t11_exists_frame_r3 (hp.basic G t L S z hctx.toSec10Ctx.toSec10Z).1 hty
  obtain ⟨⟨z', hz'L⟩, hz'⟩ := F.ψ_surj t11_zeta0_mem_P
  let D : T11Frame t L S z K1 K2 T R h z' := ⟨H, F, hF, hz'L, hz'⟩
  obtain ⟨F', htN, hF'⟩ := t11_exists_frame_r3 (t11_psp' H) (t11_type_t H)
  obtain ⟨l, -, y₁, hy₁, y₂, hy₂, h₁s, h₂s, h₁3, h₂3, hsq, hne, hcomm⟩ := t11_exists_ys D
  have h₁t : y₁ * t = t * y₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent hctx.toSec10Ctx hy₁)
  have h₂t : y₂ * t = t * y₂ :=
    Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent hctx.toSec10Ctx hy₂)
  have hprod := t11_prod_mem' H h₁s h₂s h₁3 h₂3 hsq
  have hv : y₁ * y₂ * z' ∈ CFSG.conjugate L h := Subgroup.mul_mem _ hprod (t11_zp_mem' D)
  have hvty := t11_type_v D F' hF' h₁s h₂s h₁t h₂t h₁3 h₂3 hsq hne hprod
  have huL : h * (y₁ * y₂ * z') * h⁻¹ ∈ L := (mem_conjugate_iff L h _).1 hv
  have hu := inducesTypeSome_conjugate hvty h⁻¹
  rw [t11x_conjugate_inv, inv_inv] at hu
  refine t11_no_conj_i2m hp hctx.toSec10Ctx hctx.hyp huL hu ⟨h * l * h⁻¹, ?_⟩
  calc (h * l * h⁻¹)⁻¹ * t * (h * l * h⁻¹)
      = h * (h⁻¹ * t * h) * ((h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) * l) * h⁻¹ := by group
    _ = h * (h⁻¹ * t * h) * (y₁ * y₂ * z') * h⁻¹ := by rw [hcomm]
    _ = t * (h * (y₁ * y₂ * z') * h⁻¹) := by group

end CFSG.OddStandard.SmallF3.Omega
