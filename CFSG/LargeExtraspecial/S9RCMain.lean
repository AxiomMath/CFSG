module

public import CFSG.LargeExtraspecial.S9RCData
public import CFSG.LargeExtraspecial.S10EightA
public import CFSG.LargeExtraspecial.S9PB
public import CFSG.LargeExtraspecial.S9PF
public import CFSG.LargeExtraspecial.S9PG
public import CFSG.LargeExtraspecial.S9RBQSix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RC

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem apply_sub_mem_Vt_of_spRho_zero (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {e : Vt S g t}
    (he : beta H C ht ht1 hVQ (aV ht) e = 0)
    (hbe : beta H C ht ht1 hVQ (bV (mem_Lbar_of_pair H ht hh)) e = 0)
    {yt : S.M} (hltL : S.ρ yt ∈ S.Lbar g)
    (hlte : ∀ v : Vt S g t, ((spRho (beta_isAlt H C ht ht1 hVQ) he 1 v : Vt S g t) : S.Qt) =
      ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    {f : S.O} (hfL : f ∈ S.Lbar ((h : G) * g))
    (hfe : ∀ v : Vt S g t, ((spRho (beta_isAlt H C ht ht1 hVQ) hbe 0 v : Vt S g t) : S.Qt) =
      (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vt S g t := by
  have haQ := H.conj_mem
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  have hbQ := conj_mem_QG' S h.2 haQ
  have hbV := cl_mem_Vt hth
  have haV := cl_a_mem_Vt ht
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hP.tau_not_mem
  have hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  have hab := beta_aV_bV H C ht ht1 hVQ hh hb
  have hfR : f ∈ Rbar S g t := Lbar_mul_le_Rbar hth hfL
  have hff : f * f = 1 := mul_self_of_mem_Lbar S hbQ hfL
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hffp : ∀ w : S.Qt, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
    fun w => by rw [← coe_mul_apply, hff]; rfl
  have hfa : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + (e : S.Qt) := by
    have h1 := hfe (aV ht)
    rw [spRho_apply, hab, he, zero_mul, add_zero, zero_smul, add_zero, one_smul] at h1
    exact h1.symm
  have heP : (e : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := (beta_aV_eq_zero_iff H C ht ht1 hVQ e).mp he
  set z := (f : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p with hz
  have hzW : z ∈ Wt S g t := sub_mem (apply_mem_Wt H hfR hp.2) hp.2
  have hzP : z ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) :=
    apply_sub_mem_clSub_of_mem_Wt (C.mul h) hbV hbQ hp.2 hfL
  have hv : ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) =
        (α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z := by
    intro α hα
    have hvV : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈ Vt S g t :=
      apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hPab hα hzW
    have hvPa : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈ S.clSub (S.QG ⊓ S.Qa g) :=
      RB.apply_sub_mem_clSub_Wt H C ht hα.1 hzW
    have hfαN : f * α * f⁻¹ ∈ Nbar S g t := by
      refine ⟨mul_mem (mul_mem hfR (Nbar_le_Rbar hα.2)) (inv_mem hfR), fun w hw => ?_⟩
      rw [coe_mul_apply, coe_mul_apply,
        hα.2.2 _ (apply_mem_Vt_of_mem_Rbar haQ (inv_mem hfR) hw), apply_inv_apply_O]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Lbar_apply_sub_mem_span' haQ hp.1 hα.1)
    have hfv : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) =
        ((f * α * f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p -
          c • (S.cl (g * S.z * g⁻¹) + (e : S.Qt)) := by
      rw [← hfa, ← map_smul, hc, hfinv, coe_mul_apply, coe_mul_apply, hz]
      simp only [map_sub, hffp]
      abel
    have hfvP : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) ∈
        S.clSub (S.QG ⊓ S.Qa g) := by
      rw [hfv]
      exact sub_mem (sub_mem (Nbar_apply_mem_clSub haQ H.conj_ne haV hfαN hp.1) hp.1)
        (Submodule.smul_mem _ _ (add_mem (cl_mem_clSub_self haQ) heP))
    set v : Vt S g t := ⟨(α : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z, hvV⟩ with hvdef
    have h1 : beta H C ht ht1 hVQ (aV ht) v = 0 := (beta_aV_eq_zero_iff H C ht ht1 hVQ v).mpr hvPa
    have h3 : beta H C ht ht1 hVQ (aV ht) (spRho hβ hbe 0 v) = 0 :=
      (beta_aV_eq_zero_iff H C ht ht1 hVQ _).mpr (by rw [hfe]; exact hfvP)
    have h4 : beta H C ht ht1 hVQ v e = 0 := by
      rw [spRho_apply] at h3
      simp only [map_add, map_smul, smul_eq_mul, h1, he, hab, mul_zero, zero_mul, add_zero,
        zero_add, mul_one] at h3
      exact h3
    have h5 : spRho hβ he 1 v = v := by
      rw [spRho_apply, isAlt_symm hβ v (aV ht), h1, h4]
      simp
    have h6 := hlte v
    rw [h5] at h6
    exact h6.symm
  have huP : ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    RB.apply_sub_mem_clSub_Wt H C ht hltL hzW
  have hufix : ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈
      fixSub S (S.Lbar g ⊓ Nbar S g t) := by
    refine (mem_fixSub S).mpr fun α hα => ?_
    have hcomm : α * S.ρ yt = S.ρ yt * α := Lbar_comm S haQ hα.1 hltL
    have h1 := hv α hα
    rw [map_sub, sub_eq_iff_eq_add] at h1
    rw [map_sub, ← coe_mul_apply, hcomm, coe_mul_apply, h1]
    abel
  have huV : ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈ Vt S g t := by
    have hmem : ((S.ρ yt : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := ⟨huP, hufix⟩
    rw [S8.clSub_inf_fixSub_Abar H C ht ht1 hVQ
      (card_Abar_mul_two_pow_pgl25 H C ht ht1 hVQ hP)] at hmem
    exact hmem.2
  exact mem_Vt_of_apply_sub_mem_pgl25 H hNo C ht ht1 hVQ hP hh hb he hltL hlte ⟨hzP, hzW⟩ huV

end CFSG.LargeExtraspecial.S9.RC

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem false_of_pgl25 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : False := by
  classical
  have haQ := H.conj_mem
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hn := four_lt_width_pgl25 H C ht ht1 hVQ hP hA
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  have hbQ := conj_mem_QG' S h.2 haQ
  have hVb : (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_mem_Vt hth)
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hP.tau_not_mem
  have hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  have hab := beta_aV_bV H C ht ht1 hVQ hh hb
  obtain ⟨e, he, hbe, heE, hx, hxE⟩ := RC.exists_spRho_pair_pgl25 H C ht ht1 hVQ hP hh hb
  obtain ⟨lt, hltL, hlte⟩ := mem_LmodN.mp heE
  obtain ⟨yt, -, rfl⟩ := (mem_Lbar S).mp hltL
  obtain ⟨l0, hl0L, hl0e⟩ := mem_LmodN.mp hxE
  have hkI : resV haQ t ⟨S.ρ h, hh⟩ ∈ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) :=
    RmodN_le_isometryGroup H C ht ht1 hVQ ⟨S.ρ h, hh, fun _ => rfl⟩
  have hka : resV haQ t ⟨S.ρ h, hh⟩ (aV ht) = bV hth :=
    Subtype.ext (by rw [coe_resV_apply]; exact ρ_cl_conj_z S h haQ)
  have hke : resV haQ t ⟨S.ρ h, hh⟩ ((resV haQ t ⟨S.ρ h, hh⟩)⁻¹ e) = e :=
    (resV haQ t ⟨S.ρ h, hh⟩).apply_symm_apply e
  have hconj : resV haQ t ⟨S.ρ h, hh⟩ * spRho hβ hx 0 * (resV haQ t ⟨S.ρ h, hh⟩)⁻¹ =
      spRho hβ hbe 0 := by
    rw [conj_spRho hβ hx 0 hkI (by rw [hka, hke]; exact hbe)]
    exact spRho_congr hβ _ _ hka hke rfl
  have hfL : S.ρ h * l0 * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := by
    rw [Lbar_mul S h g]; exact ⟨l0, hl0L, rfl⟩
  have hfe : ∀ v : Vt S g t, ((spRho hβ hbe 0 v : Vt S g t) : S.Qt) =
      ((S.ρ h * l0 * (S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro v
    rw [← hconj, coe_mul_apply, coe_mul_apply]
    change ((resV haQ t ⟨S.ρ h, hh⟩ (spRho hβ hx 0 ((resV haQ t ⟨S.ρ h, hh⟩)⁻¹ v)) :
      Vt S g t) : S.Qt) = _
    rw [coe_resV_apply, hl0e, ← map_inv, coe_resV_apply]
    rfl
  have hfW : ∀ w ∈ Wt S g t,
      ((S.ρ h * l0 * (S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro w hw
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.mp ((sup_eq_Wt H C ht ht1 hVQ hh hb hPab).ge hw)
    have h1 := RC.apply_sub_mem_Vt_of_spRho_zero H hNo C ht ht1 hVQ hP hh hb he hbe hltL hlte
      hfL hfe hp
    have h2 := hVb (Lbar_apply_sub_mem_span' hbQ hq.1 hfL)
    rw [map_add, add_sub_add_comm]
    exact add_mem h1 h2
  have hl0fix : ∀ w ∈ Wt S g t, (l0 : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro w hw
    have h1 := hfW _ (apply_mem_Wt H hh hw)
    rw [coe_mul_apply, coe_mul_apply, inv_apply_apply_O] at h1
    have h2 := apply_mem_Vt_of_mem_Rbar haQ (inv_mem hh) h1
    rwa [map_sub, inv_apply_apply_O, inv_apply_apply_O] at h2
  have hl0N : l0 ∉ Nbar S g t := by
    intro hN
    have h1 := hfe (aV ht)
    rw [spRho_apply, hab, he, zero_mul, add_zero, zero_smul, add_zero, one_smul, coe_mul_apply,
      coe_mul_apply, hN.2 _ (apply_mem_Vt_of_mem_Rbar haQ (inv_mem hh) (aV ht).2),
      apply_inv_apply_O] at h1
    have h2 : aV ht + e = aV ht := Subtype.ext h1
    rw [add_eq_left] at h2
    apply hP.tau_not_mem
    have := heE
    rw [spRho_congr hβ he (map_zero _) rfl h2 rfl, spRho_zero_one] at this
    exact this
  exact false_of_fix_WV_pgl25 H C ht ht1 hVQ hP hNo hn hl0L hl0N hl0fix

theorem Lbar_inf_Nbar_eq_pgl25 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) : S.Lbar g ⊓ Nbar S g t = zpowers t := by
  by_contra hA
  exact false_of_pgl25 H hNo C ht ht1 hVQ hP hA

theorem pgl25ConjResidual : PGL25ConjResidual.{u} := by
  intro G _ _ S g _ _ _ H hNo C t ht ht1 hVQ hP hA
  exact (hA (Lbar_inf_Nbar_eq_pgl25 H hNo C ht ht1 hVQ hP)).elim

end CFSG.LargeExtraspecial.S9

namespace CFSG.LargeExtraspecial.S10

universe u

theorem noPGL25 {G : Type u} [Group G] [Finite G] (S : Setting G) (g : G) : NoPGL25 S g := by
  intro H hNo C τ hτ hτ1 hVQ _ hA hP
  exact hA (S9.Lbar_inf_Nbar_eq_pgl25 H hNo C hτ hτ1 hVQ hP)

end CFSG.LargeExtraspecial.S10
