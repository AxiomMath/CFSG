module

public import CFSG.LargeExtraspecial.S4EightF6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_conj_LmodN_le (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {r : S.O} (hr : r ∈ Rbar S g t) {X : Subgroup S.O}
    (hX : (S.Lbar g).map (MulAut.conj r).toMonoidHom ≤ X) :
    (LmodN S g t).map (MulAut.conj (resV haQ t ⟨r, hr⟩)).toMonoidHom ≤
      (X.subgroupOf (Rbar S g t)).map (resV haQ t) := by
  rw [← map_subgroupOf_resV haQ ht]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  refine ⟨⟨r, hr⟩ * l * ⟨r, hr⟩⁻¹, ?_, ?_⟩
  · show ((⟨r, hr⟩ * l * ⟨r, hr⟩⁻¹ : Rbar S g t) : S.O) ∈ X
    exact hX ⟨l, hl, rfl⟩
  · show resV haQ t (⟨r, hr⟩ * l * ⟨r, hr⟩⁻¹) =
      resV haQ t ⟨r, hr⟩ * resV haQ t l * (resV haQ t ⟨r, hr⟩)⁻¹
    rw [map_mul, map_mul, map_inv]

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H C ht ht1 hVQ

theorem RmodN_eq_closure_of_beta (hNo : NoA2 S g)
    (hcase : SpCase H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ)
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (he : e ∈ RmodN S g t)
    (hb : beta H C ht ht1 hVQ (aV ht) (e (aV ht)) = 1) :
    RmodN S g t = closure ((LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) ∪
      (LmodN S g t).map (MulAut.conj e).toMonoidHom) := by
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  rcases hcase with hSp | hΩ
  · have heI : e ∈ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := hSp.eq_sp ▸ he
    have hgen := S2.spFix_eq_closure_spRadFix hβ hnd (F := ⊥) (bot_inf_eq _) (m := k)
      (by rw [S2.spPerp_bot, finrank_top, hk]; ring) (by rw [S2.spPerp_bot]; trivial)
      (by rw [S2.spPerp_bot]; trivial) hb
    rw [S2.spFix_bot, S2.spRadFix_bot, S2.spRadFix_bot] at hgen
    rw [hSp.eq_sp, hgen, hSp.LmodN_eq, map_conj_spPointRadical hβ heI]
  · obtain ⟨Q, hQ, hQβ, hX, hE, hsing⟩ := hΩ.exists_form
    have heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (omegaGroup_le Q hQ) (hX ▸ he)
    have hpol : polar Q (aV ht) (e (aV ht)) = 1 := by
      rw [← polarBilin_apply_apply, hQβ]
      exact hb
    have hQa : Q (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
    have hQe : Q (e (aV ht)) = 0 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup heO, hQa]
    have hgen := S2.omegaFix_eq_closure_radFix hQ (F := ⊥) (bot_inf_eq _) (m := k) (by omega)
      (by rw [S2.perp_bot, finrank_top, hk]; ring) (by rw [S2.perp_bot]; trivial)
      (by rw [S2.perp_bot]; trivial) (aV_ne_zero H ht) hQa hQe hpol
    rw [S2.omegaFix_bot, S2.radFix_bot, S2.radFix_bot] at hgen
    rw [hX, hgen, hE, map_conj_pointRadical heO]

omit C ht1 hVQ in
theorem Rbar_le_sup_Nbar {r : S.O} (hr : r ∈ Rbar S g t)
    (hgen : RmodN S g t ≤ closure ((LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) ∪
      (LmodN S g t).map (MulAut.conj (resV H.conj_mem t ⟨r, hr⟩)).toMonoidHom)) :
    Rbar S g t ≤ (S.Lbar g ⊔ (S.Lbar g).map (MulAut.conj r).toMonoidHom) ⊔ Nbar S g t := by
  have haQ := H.conj_mem
  set X := S.Lbar g ⊔ (S.Lbar g).map (MulAut.conj r).toMonoidHom with hX
  have himg : RmodN S g t ≤ (X.subgroupOf (Rbar S g t)).map (resV haQ t) := by
    refine hgen.trans ((closure_le _).mpr ?_)
    rintro e (he | he)
    · rw [← map_subgroupOf_resV haQ ht] at he
      obtain ⟨l, hl, rfl⟩ := he
      exact ⟨l, mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hl)), rfl⟩
    · exact map_conj_LmodN_le haQ ht hr le_sup_right he
  intro y hy
  obtain ⟨x, hx, hxy⟩ := himg ⟨y, hy, fun v => coe_resV_apply haQ ⟨y, hy⟩ v⟩
  have hxyN : ((x⁻¹ * ⟨y, hy⟩ : Rbar S g t) : S.O) ∈ Nbar S g t := by
    rw [← resV_eq_one_iff haQ, map_mul, map_inv, hxy, inv_mul_cancel]
  have : y = (x : S.O) * ((x⁻¹ * ⟨y, hy⟩ : Rbar S g t) : S.O) := by simp
  rw [this]
  exact mul_mem (mem_sup_left (mem_subgroupOf.mp hx)) (mem_sup_right hxyN)

end CFSG.LargeExtraspecial.S4
