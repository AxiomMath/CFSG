module

public import CFSG.LargeExtraspecial.S9RCPair
public import CFSG.LargeExtraspecial.S9RBQPar
public import CFSG.LargeExtraspecial.S6TwoD
public import CFSG.LargeExtraspecial.S9FourC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RC

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_spRho_pair_pgl25 (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    ∃ e : Vt S g t, ∃ he : beta H C ht ht1 hVQ (aV ht) e = 0,
      beta H C ht ht1 hVQ (bV (mem_Lbar_of_pair H ht hh)) e = 0 ∧
      spRho (beta_isAlt H C ht ht1 hVQ) he 1 ∈ LmodN S g t ∧
      ∃ hx : beta H C ht ht1 hVQ (aV ht) ((resV H.conj_mem t ⟨S.ρ h, hh⟩)⁻¹ e) = 0,
        spRho (beta_isAlt H C ht ht1 hVQ) hx 0 ∈ LmodN S g t := by
  classical
  have haQ := H.conj_mem
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  have hka : resV haQ t ⟨S.ρ h, hh⟩ (aV ht) = bV hth :=
    Subtype.ext (by rw [coe_resV_apply]; exact ρ_cl_conj_z S h haQ)
  have hab := beta_aV_bV H C ht ht1 hVQ hh hb
  have hba : beta H C ht ht1 hVQ (bV hth) (aV ht) = 1 := by rw [isAlt_symm hβ, hab]
  obtain ⟨e₀, he₀, he₀E⟩ := RB.exists_spRho_one_mem_LmodN_pgl25 H C ht ht1 hVQ hP
  have he : beta H C ht ht1 hVQ (aV ht)
      (e₀ + beta H C ht ht1 hVQ (bV hth) e₀ • aV ht) = 0 := by
    rw [map_add, map_smul, he₀, hβ.self_eq_zero, smul_zero, add_zero]
  have hbe : beta H C ht ht1 hVQ (bV hth)
      (e₀ + beta H C ht ht1 hVQ (bV hth) e₀ • aV ht) = 0 := by
    rw [map_add, map_smul, hba, smul_eq_mul, mul_one]
    exact zmod2_add_self _
  have heE : spRho hβ he 1 ∈ LmodN S g t := by
    rw [spRho_add_smul hβ he₀ 1 _ he]; exact he₀E
  obtain ⟨d, hd, hdA, hdE⟩ := hP.exists_typeA
  have hkX : resV haQ t ⟨S.ρ h, hh⟩ ∈ RmodN S g t := ⟨S.ρ h, hh, fun _ => rfl⟩
  obtain ⟨hx, hxE⟩ := spRho_zero_mem_of_conj hβ hnd hP.finrank_eq (aV_ne_zero H ht)
    (RmodN_le_isometryGroup H C ht ht1 hVQ) (LmodN_le_RmodN ht)
    (LmodN_le_spPointRadical H C ht ht1 hVQ) (card_spPointRadical_le_two_mul H C ht ht1 hVQ)
    hP.tau_not_mem hP.transitive (fun x hx hxa => mem_normalizer_LmodN H ht hx hxa)
    hd hdA hdE he heE hkX (by rw [hka]; exact hab) (by rw [hka]; exact hbe)
  exact ⟨_, he, hbe, heE, hx, hxE⟩

theorem mem_Vt_of_apply_sub_mem_pgl25 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {e : Vt S g t}
    (he : beta H C ht ht1 hVQ (aV ht) e = 0) {y : S.M} (hl : S.ρ y ∈ S.Lbar g)
    (hle : ∀ v : Vt S g t, ((spRho (beta_isAlt H C ht ht1 hVQ) he 1 v : Vt S g t) : S.Qt) =
      ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    {q : S.Qt} (hq : q ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t)
    (hlq : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t) : q ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hP.tau_not_mem
  have hth := mem_Lbar_of_pair H ht hh
  have hbQ := conj_mem_QG' S h.2 haQ
  have hVb : (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_mem_Vt hth)
  have hyR : S.ρ y ∈ Rbar S g t := Lbar_le_Rbar ht hl
  have hfix : ∀ l'' ∈ S.Lbar ((y : G) * ((h : G) * g)),
      (l'' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S ((h : G) * g) t := by
    intro l'' hl''
    rw [Vt_mul]
    rw [Lbar_mul S y ((h : G) * g)] at hl''
    obtain ⟨l', hl', rfl⟩ := hl''
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hl'R : l' ∈ Rbar S g t := Lbar_mul_le_Rbar hth hl'
    have hinv : (((S.ρ y)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t := by
      have h2 := apply_mem_Vt_of_mem_Rbar haQ (inv_mem hyR) hlq
      rw [map_sub, inv_apply_apply_O] at h2
      have := neg_mem h2
      rwa [neg_sub] at this
    have hl'q : (l' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t :=
      hVb (Lbar_apply_sub_mem_span' hbQ hq.1 hl')
    have e : ((S.ρ y * l' * (S.ρ y)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q =
        (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) +
          ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) +
            (l' : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((((S.ρ y)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q)) := by
      rw [coe_mul_apply, coe_mul_apply]
      simp only [map_add, map_sub]
      abel
    rw [e]
    exact add_mem hlq (apply_mem_Vt_of_mem_Rbar haQ hyR
      (add_mem hl'q (apply_mem_Vt_of_mem_Rbar haQ hl'R hinv)))
  have hVQ' := not_V_le_Qa_mul H hVQ hh
  have hyR' : S.ρ y ∈ Rbar S ((h : G) * g) t := by rw [Rbar_mul]; exact hyR
  have hb' : (y : G) * ((h : G) * g) * S.z * ((y : G) * ((h : G) * g))⁻¹ ∉
      S.Qa ((h : G) * g) := by
    have := not_mem_Qa_of_spRho_one H C ht ht1 hVQ hh hb he hle
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hR' := hR.mul H hh
  have hPI' := pairInt_of_radBound (H.mul h) (C.mul h) hth ht1 hVQ' hR'
  have hPbb := clSub_inf_clSub_le_Vt (H.mul h) (C.mul h) hth ht1 hVQ' hyR' hb' hR'
  have hqW : q ∈ Wt S ((h : G) * g) t := by rw [Wt_mul]; exact hq.2
  have hq₂ := (forall_apply_sub_mem_Vt_iff_b (H.mul h) (hNo.mul h) (C.mul h) hth ht1 hVQ'
    hyR' hb' hPI' hqW).mp hfix
  have hint := sup_Vt_inf_sup_Vt (H.mul h) (C.mul h) hth ht1 hVQ' hyR' hb' hPbb
  have hq₁ : q ∈ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S ((h : G) * g) t) ⊔
      Vt S ((h : G) * g) t := Submodule.mem_sup_left ⟨hq.1, hqW⟩
  have hqV' : q ∈ Vt S ((h : G) * g) t := hint ▸ ⟨hq₁, hq₂⟩
  rwa [Vt_mul] at hqV'

end CFSG.LargeExtraspecial.S9.RC
