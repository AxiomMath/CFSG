module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.CharacterTheory.PSL2Table.Tori
import CFSG.GH74.GLS.IVK.L2.BorelMatrices

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL2Table CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups Pointwise

section Field

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
private theorem psl2FieldAut_mk_unip (σ : F ≃+* F) (t : F) :
    psl2FieldAut F σ (mk (unip t)) = mk (unip (σ t)) := by
  have h : Matrix.SpecialLinearGroup.map σ.toRingHom (unip t) = unip (σ t) := by
    apply SL_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) =
    QuotientGroup.mk' (Subgroup.center _) (unip (σ t))
  rw [psl2RingEquiv_mk, h]

theorem exists_eq_conj_of_forall_unipotent (h2 : (2 : F) ≠ 0) (α : MulAut PSL(2, F))
    (hα : ∀ u ∈ unipotent F, α u = u) : ∃ u ∈ unipotent F, α = MulAut.conj u := by
  obtain ⟨x, rfl⟩ := (semilinearEquivAut F).surjective α
  have hx : semilinearEquivAut F x = pglAction F x.left * psl2FieldAut F x.right := by
    change semilinearAction F x = _
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  rw [hx] at hα ⊢
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (hα _ (mk_unip_mem_unipotent 1))
  rw [MulAut.mul_apply, psl2FieldAut_mk_unip, map_one, toPGL_pglAction] at h1
  obtain ⟨c, hc⟩ := GH74.GLS.IVK.L2Borel.exists_eq_toPGL_of_commute one_ne_zero
    (mul_inv_eq_iff_eq_mul.mp h1)
  have hg : pglAction F x.left = MulAut.conj (mk (unip c)) := by rw [hc, pglAction_toPGL]
  have hσ : x.right = 1 := by
    ext t
    have ht := hα _ (mk_unip_mem_unipotent t)
    rw [MulAut.mul_apply, psl2FieldAut_mk_unip, hg, MulAut.conj_apply,
      unipotent_mul_comm (mk_unip_mem_unipotent c) (mk_unip_mem_unipotent _),
      mul_inv_cancel_right, mk_unip_eq_mk_unip_iff h2] at ht
    exact ht
  refine ⟨mk (unip c), mk_unip_mem_unipotent c, ?_⟩
  rw [hg, hσ, map_one, mul_one]

end Field

theorem kFactL2UnipotentCentralizer : KFactL2UnipotentCentralizer := by
  intro p n _ hp2 hn U α hα
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U₀, hU₀⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (PSL2GF p n) U₀ U
  have hmem : ∀ x, x ∈ ((g • U₀ : Sylow p (PSL2GF p n)) : Subgroup (PSL2GF p n)) ↔
      g⁻¹ * x * g ∈ unipotent (GaloisField p n) := by
    intro x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  set β : MulAut (PSL2GF p n) := (MulAut.conj g)⁻¹ * α * MulAut.conj g with hβdef
  have hβ : ∀ u ∈ unipotent (GaloisField p n), β u = u := by
    intro u hu
    have h := hα (g * u * g⁻¹) ((hmem _).mpr (by simpa [mul_assoc] using hu))
    simp only [hβdef, MulAut.mul_apply, MulAut.conj_apply, h]
    simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]
  obtain ⟨u, hu, hβu⟩ := exists_eq_conj_of_forall_unipotent (Ring.two_ne_zero hF) β hβ
  refine ⟨g * u * g⁻¹, (hmem _).mpr (by simpa [mul_assoc] using hu), ?_⟩
  have hα' : α = MulAut.conj g * β * (MulAut.conj g)⁻¹ := by rw [hβdef]; group
  rw [hα', hβu, ← map_inv, ← map_mul, ← map_mul]

end CFSG.AGLEmbedding
