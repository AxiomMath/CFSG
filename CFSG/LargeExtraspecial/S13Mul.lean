module

public import CFSG.LargeExtraspecial.S10Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g' : G} {h : S.M} {t τ : S.O}

theorem mem_Vt_mul_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) {v : S.Qt} :
    v ∈ Vt S g' τ ↔ (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  subst hg hτ
  rw [Vt_mul]
  exact mem_Vt_conj haQ h

@[expose] noncomputable def kappaMul (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) : Vt S g t ≃ₗ[ZMod 2] Vt S g' τ where
  toFun v := ⟨((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_Vt_mul_iff haQ hg hτ).mpr (by
    rw [inv_apply_apply_O]; exact v.2)⟩
  invFun v := ⟨(((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_Vt_mul_iff haQ hg hτ).mp v.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  left_inv v := Subtype.ext (inv_apply_apply_O _ _)
  right_inv v := Subtype.ext (apply_inv_apply_O _ _)

theorem coe_kappaMul (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (v : Vt S g t) :
    ((kappaMul haQ hg hτ v : Vt S g' τ) : S.Qt) = ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem coe_kappaMul_symm (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (v : Vt S g' τ) :
    (((kappaMul haQ hg hτ).symm v : Vt S g t) : S.Qt) =
      (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := rfl

theorem Rbar_mul_conj (hg : g' = (h : G) * g) (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) :
    Rbar S g' τ = (Rbar S g t).map (cK S h) := by
  subst hg hτ
  rw [Rbar_mul, Rbar_conj]

theorem Nbar_mul_conj (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) : Nbar S g' τ = (Nbar S g t).map (cK S h) := by
  subst hg hτ
  rw [Nbar_mul, Nbar_conj haQ]

theorem Lbar_mul' (hg : g' = (h : G) * g) : S.Lbar g' = (S.Lbar g).map (cK S h) := by
  subst hg
  exact Lbar_mul S h g

theorem mem_Lbar_mul' (hg : g' = (h : G) * g) (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹)
    (ht : t ∈ S.Lbar g) : τ ∈ S.Lbar g' := by
  subst hg hτ
  exact conj_mem_Lbar_mul S h ht

theorem RmodN_mul (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) :
    RmodN S g' τ = (RmodN S g t).map (LinearEquiv.autCongr (kappaMul haQ hg hτ)).toMonoidHom := by
  have hR := Rbar_mul_conj hg hτ
  ext e
  constructor
  · rintro ⟨x, hx, hex⟩
    rw [hR, mem_map_cK_iff] at hx
    refine ⟨(LinearEquiv.autCongr (kappaMul haQ hg hτ)).symm e, ⟨_, hx, fun v => ?_⟩, by simp⟩
    rw [LinearEquiv.autCongr_symm_apply_apply, coe_kappaMul_symm, hex, coe_kappaMul]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  · rintro ⟨e', ⟨x, hx, hex⟩, rfl⟩
    refine ⟨S.ρ h * x * (S.ρ h)⁻¹, ?_, fun v => ?_⟩
    · rw [hR]
      exact ⟨x, hx, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply, coe_kappaMul, hex,
        coe_kappaMul_symm, Subgroup.coe_mul, LinearEquiv.mul_apply]

theorem LmodN_mul (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) :
    LmodN S g' τ = (LmodN S g t).map (LinearEquiv.autCongr (kappaMul haQ hg hτ)).toMonoidHom := by
  have hL := Lbar_mul' (S := S) hg
  ext e
  constructor
  · rintro ⟨x, hx, hex⟩
    rw [hL, mem_map_cK_iff] at hx
    refine ⟨(LinearEquiv.autCongr (kappaMul haQ hg hτ)).symm e, ⟨_, hx, fun v => ?_⟩, by simp⟩
    rw [LinearEquiv.autCongr_symm_apply_apply, coe_kappaMul_symm, hex, coe_kappaMul]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  · rintro ⟨e', ⟨x, hx, hex⟩, rfl⟩
    refine ⟨S.ρ h * x * (S.ρ h)⁻¹, by rw [hL]; exact ⟨x, hx, rfl⟩, fun v => ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply, coe_kappaMul, hex,
      coe_kappaMul_symm, Subgroup.coe_mul, LinearEquiv.mul_apply]

theorem kappaMul_aV (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (ht : t ∈ S.Lbar g) (ht' : τ ∈ S.Lbar g') :
    kappaMul haQ hg hτ (aV ht) = aV ht' := by
  apply Subtype.ext
  rw [coe_kappaMul]
  change ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g' * S.z * g'⁻¹)
  rw [ρ_cl_conj_z S h haQ, hg]

theorem mem_orbitOf_kappaMul (haQ : g * S.z * g⁻¹ ∈ S.QG) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (ht : t ∈ S.Lbar g) (ht' : τ ∈ S.Lbar g') (v : Vt S g' τ) :
    v ∈ orbitOf (RmodN S g' τ) (aV ht') ↔
      (kappaMul haQ hg hτ).symm v ∈ orbitOf (RmodN S g t) (aV ht) := by
  rw [RmodN_mul haQ hg hτ, ← kappaMul_aV haQ hg hτ ht ht']
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, by simp⟩
  · rintro ⟨e, he, hev⟩
    refine ⟨LinearEquiv.autCongr (kappaMul haQ hg hτ) e, ⟨e, he, rfl⟩, ?_⟩
    simp [hev]

theorem hyp4_mul (H : Hyp4 S g) (hg : g' = (h : G) * g) : Hyp4 S g' := by
  subst hg; exact H.mul h

theorem cons311_mul (C : Cons311 S g) (hg : g' = (h : G) * g) : Cons311 S g' := by
  subst hg; exact C.mul h

theorem noA2_mul (hNo : NoA2 S g) (hg : g' = (h : G) * g) : NoA2 S g' := by
  subst hg; exact hNo.mul h

theorem beta_kappaMul (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (H' : Hyp4 S g') (C' : Cons311 S g')
    (hg : g' = (h : G) * g) (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (ht' : τ ∈ S.Lbar g')
    (ht1' : τ ≠ 1) (hVQ' : ¬ V S g' τ ≤ S.Qa g') (x y : Vt S g t) :
    beta H' C' ht' ht1' hVQ' (kappaMul H.conj_mem hg hτ x) (kappaMul H.conj_mem hg hτ y) =
      beta H C ht ht1 hVQ x y := by
  obtain ⟨y', hy'⟩ := exists_t_sub_eq H C ht ht1 hVQ y
  have hy'' : ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y') - ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y' =
      ((kappaMul H.conj_mem hg hτ y : Vt S g' τ) : S.Qt) := by
    rw [coe_kappaMul, ← hy', map_sub, hτ]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inv_apply_apply_O]
  rw [beta_apply H' C' ht' ht1' hVQ' _ _ hy'', beta_apply H C ht ht1 hVQ _ _ hy', coe_kappaMul]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ h).2 _ _

theorem not_V_le_Qa_mul (H : Hyp4 S g) (hVQ : ¬ V S g t ≤ S.Qa g) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) : ¬ V S g' τ ≤ S.Qa g' := by
  intro hle
  apply hVQ
  have H' := hyp4_mul H hg
  rw [V_le_Qa_iff H'.conj_mem H'.conj_ne] at hle
  rw [V_le_Qa_iff H.conj_mem H.conj_ne]
  intro v hv
  have hv' : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g' τ := by
    rw [mem_Vt_mul_iff H.conj_mem hg hτ, inv_apply_apply_O]
    exact hv
  have h1 := hle hv'
  subst hg
  rw [QG_inf_Qa_mul h, mem_clSub_map_conj_iff h inf_le_left, inv_apply_apply_O] at h1
  exact h1

theorem conj_ne_one (ht1 : t ≠ 1) (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) : τ ≠ 1 := by
  intro e
  apply ht1
  rw [hτ] at e
  have := congrArg (fun x => (S.ρ h)⁻¹ * x * S.ρ h) e
  simpa [mul_assoc] using this

theorem polarBilin_comp_symm {U U' : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup U'] [Module (ZMod 2) U'] {Q : QuadraticForm (ZMod 2) U}
    {B : LinearMap.BilinForm (ZMod 2) U} {B' : LinearMap.BilinForm (ZMod 2) U'}
    (κ : U ≃ₗ[ZMod 2] U') (hQ : Q.polarBilin = B) (hB : ∀ x y, B' (κ x) (κ y) = B x y) :
    (Q.comp κ.symm.toLinearMap).polarBilin = B' := by
  ext u v
  have h1 := hB (κ.symm u) (κ.symm v)
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [h1, ← hQ, polarBilin_apply_apply, polarBilin_apply_apply]
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]

theorem omegaCase_mul (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (H' : Hyp4 S g') (C' : Cons311 S g') (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) (ht' : τ ∈ S.Lbar g') (ht1' : τ ≠ 1)
    (hVQ' : ¬ V S g' τ ≤ S.Qa g') : OmegaCase H' C' ht' ht1' hVQ' := by
  obtain ⟨Q, hQ, hpol, hRQ, hLQ, hsing⟩ := hΩ.exists_form
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = kappaMul H.conj_mem hg hτ := ⟨_, rfl⟩
  have hbk : ∀ x y, beta H' C' ht' ht1' hVQ' (κ x) (κ y) = beta H C ht ht1 hVQ x y :=
    fun x y => by rw [hκ]; exact beta_kappaMul H C ht ht1 hVQ H' C' hg hτ ht' ht1' hVQ' x y
  have hRconj : RmodN S g' τ = (RmodN S g t).map (LinearEquiv.autCongr κ).toMonoidHom := by
    rw [hκ]; exact RmodN_mul H.conj_mem hg hτ
  have hLconj : LmodN S g' τ = (LmodN S g t).map (LinearEquiv.autCongr κ).toMonoidHom := by
    rw [hκ]; exact LmodN_mul H.conj_mem hg hτ
  have hκaV : κ (aV ht) = aV ht' := by rw [hκ]; exact kappaMul_aV H.conj_mem hg hτ ht ht'
  have horb : ∀ v, v ∈ orbitOf (RmodN S g' τ) (aV ht') ↔
      κ.symm v ∈ orbitOf (RmodN S g t) (aV ht) := fun v => by
    rw [hκ]; exact mem_orbitOf_kappaMul H.conj_mem hg hτ ht ht' v
  have hpolτ : (Q.comp κ.symm.toLinearMap).polarBilin = beta H' C' ht' ht1' hVQ' :=
    polarBilin_comp_symm κ hpol hbk
  have hQτnd : (Q.comp κ.symm.toLinearMap).polarBilin.Nondegenerate :=
    hpolτ ▸ beta_nondegenerate H' C' ht' ht1' hVQ'
  obtain ⟨h1, h2, h3⟩ := transport_omega_data hQ hRQ hLQ hsing hQτnd
  rw [← hRconj] at h1 h3
  rw [← hLconj, hκaV] at h2
  rw [hκaV] at h3
  refine ⟨?_, ⟨_, hQτnd, hpolτ, h1, h2, h3⟩⟩
  obtain ⟨v, hv0, hv⟩ := hΩ.not_transitive
  refine ⟨κ v, fun e => hv0 (κ.injective (e.trans (map_zero _).symm)), ?_⟩
  rw [horb, LinearEquiv.symm_apply_apply]
  exact hv

theorem hyp10_mul (X : Hyp10 S g t) (hg : g' = (h : G) * g)
    (hτ : τ = S.ρ h * t * (S.ρ h)⁻¹) : Hyp10 S g' τ := by
  have hRc := Rbar_mul_conj (S := S) hg hτ
  have hNc := Nbar_mul_conj X.haQ hg hτ
  have hLc := Lbar_mul' (S := S) hg
  have ht' := mem_Lbar_mul' hg hτ X.ht
  have ht1' := conj_ne_one X.ht1 hτ
  have hVQ' := not_V_le_Qa_mul X.H X.hVQ hg hτ
  refine ⟨hyp4_mul X.H hg, noA2_mul X.hNo hg, cons311_mul X.C hg, ht', ht1', ?_, ?_, hVQ',
    omegaCase_mul X.H X.C X.ht X.ht1 X.hVQ X.hΩ _ _ hg hτ ht' ht1' hVQ', ?_, ?_⟩
  · intro e
    apply X.hR
    rw [hRc, hLc] at e
    exact Subgroup.map_injective (cK_injective h) e
  · intro e
    apply X.hA
    rw [hNc, hLc, ← Subgroup.map_inf_eq _ _ _ (cK_injective h)] at e
    have e2 : zpowers τ = (zpowers t).map (cK S h) := by
      rw [MonoidHom.map_zpowers, cK_apply, hτ]
    rw [e2] at e
    exact Subgroup.map_injective (cK_injective h) e
  · rw [← LinearEquiv.finrank_eq (kappaMul X.H.conj_mem hg hτ), X.h4]
  · obtain ⟨W, hW, hWs⟩ := X.plus
    refine ⟨W.map (kappaMul X.H.conj_mem hg hτ).toLinearMap,
      by rw [LinearEquiv.finrank_map_eq, hW], ?_⟩
    rintro _ ⟨w, hw, rfl⟩ hw0
    rw [mem_orbitOf_kappaMul X.H.conj_mem hg hτ X.ht ht']
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hWs w hw fun e => hw0 (by rw [e]; exact map_zero _)

end CFSG.LargeExtraspecial.S13
