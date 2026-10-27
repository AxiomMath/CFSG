module

public import CFSG.LargeExtraspecial.S6TwoA
public import CFSG.LargeExtraspecial.S6Five
public import CFSG.LargeExtraspecial.S6OneC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def R0bar (h : S.M) : Subgroup S.O :=
  S.Lbar g ⊔ S.Lbar ((h : G) * g)

section A6

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hA : A6Case H C ht ht1 hVQ)
include H C ht ht1 hVQ hA

theorem card_spPointRadical_eq_two_mul_a6 :
    Nat.card (spPointRadical (beta H C ht ht1 hVQ) (aV ht)) = 2 * Nat.card (LmodN S g t) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hle := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hlt : LmodN S g t < spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
    lt_of_le_of_ne hle fun h => hA.tau_not_mem (h ▸ spTransvection_mem_U _ _)
  have h1 := card_spPointRadical_le_two_mul H C ht ht1 hVQ
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card (LmodN S g t) := Nat.card_pos
  rw [hk] at h1 h2 ⊢
  have hk1 : 1 < k := by
    by_contra hk1
    push Not at hk1
    have : Nat.card (LmodN S g t) * k ≤ Nat.card (LmodN S g t) * 1 :=
      Nat.mul_le_mul_left _ hk1
    omega
  have hk2 : k ≤ 2 := by
    have : Nat.card (LmodN S g t) * k ≤ Nat.card (LmodN S g t) * 2 := by linarith
    exact Nat.le_of_mul_le_mul_left this hpos
  have : k = 2 := by omega
  rw [this, mul_comm]

section Pair

variable {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
include hh

theorem LhmodN_props_a6 :
    LhmodN S g t h ≤ spPointRadical (beta H C ht ht1 hVQ) (bV (mem_Lbar_of_pair H ht hh)) ∧
      Nat.card (spPointRadical (beta H C ht ht1 hVQ) (bV (mem_Lbar_of_pair H ht hh))) =
        2 * Nat.card (LhmodN S g t h) ∧
      spTransvection _ (beta_isAlt H C ht ht1 hVQ) (bV (mem_Lbar_of_pair H ht hh)) ∉
        LhmodN S g t h ∧
      ∀ d (hd : beta H C ht ht1 hVQ (bV (mem_Lbar_of_pair H ht hh)) d = 0),
        d ∉ (ZMod 2) ∙ bV (mem_Lbar_of_pair H ht hh) →
          spRho (beta_isAlt H C ht ht1 hVQ) hd 0 ∉ LhmodN S g t h := by
  have hth := mem_Lbar_of_pair H ht hh
  set β := beta H C ht ht1 hVQ with hβdef
  have hβa : β.IsAlt := beta_isAlt H C ht ht1 hVQ
  have hnd : β.Nondegenerate := beta_nondegenerate H C ht ht1 hVQ
  set e := resV H.conj_mem t ⟨S.ρ h, hh⟩ with he
  have heR : e ∈ RmodN S g t := by rw [← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have hea : e (aV ht) = bV hth := resV_aV H.conj_mem ht hh hth
  have heI : e ∈ TauCeti.BilinForm.isometryGroup β := RmodN_le_isometryGroup H C ht ht1 hVQ heR
  have heb : e⁻¹ (bV hth) = aV ht := by
    rw [← hea]
    exact e.symm_apply_apply _
  have hL := LhmodN_eq_map_conj H ht hth heR hea
  have hLU := LmodN_le_spPointRadical H C ht ht1 hVQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL]
    rintro _ ⟨w, hw, rfl⟩
    have := conj_mem_spPointRadical hβa heI (hLU hw)
    rwa [hea] at this
  · rw [hL, card_map_of_injective (MulAut.conj e).injective,
      ← card_spPointRadical_eq_two_mul_a6 H C ht ht1 hVQ hA,
      card_spPointRadical hβa hnd (bV_ne_zero H hth), card_spPointRadical hβa hnd (aV_ne_zero H ht)]
  · rw [hL]
    rintro ⟨w, hw, hwe⟩
    have h1 : w = e⁻¹ * spTransvection β hβa (bV hth) * e⁻¹⁻¹ := by
      rw [← hwe]
      simp [mul_assoc]
    rw [conj_spTransvection hβa _ (inv_mem heI), heb] at h1
    exact hA.tau_not_mem (h1 ▸ hw)
  · intro d hd hdb
    rw [hL]
    rintro ⟨w, hw, hwe⟩
    have hd' : β (e⁻¹ (bV hth)) (e⁻¹ d) = 0 :=
      (TauCeti.BilinForm.mem_isometryGroup_iff.mp (inv_mem heI) (bV hth) d).trans hd
    have hd'' : β (aV ht) (e⁻¹ d) = 0 := by rwa [heb] at hd'
    have h1 : w = e⁻¹ * spRho hβa hd 0 * e⁻¹⁻¹ := by
      rw [← hwe]
      simp [mul_assoc]
    rw [conj_spRho hβa hd 0 (inv_mem heI) hd'] at h1
    have h2 : spRho hβa hd' 0 = spRho hβa hd'' 0 := by
      ext x
      simp only [spRho_apply, heb]
    rw [h2] at h1
    have hnot : e⁻¹ d ∉ (ZMod 2) ∙ aV ht := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      apply hdb
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      have := congrArg e hc
      rwa [map_smul, hea, show e (e⁻¹ d) = d from e.apply_symm_apply d] at this
    exact hA.no_typeA (e⁻¹ d) hd'' hnot (h1 ▸ hw)

variable (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hb

theorem exists_minus_form_a6 :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate),
      Q.polarBilin = beta H C ht ht1 hVQ ∧ Q (aV ht) = 0 ∧
      Q (bV (mem_Lbar_of_pair H ht hh)) = 0 ∧
      (∃ u, beta H C ht ht1 hVQ (aV ht) u = 0 ∧
        beta H C ht ht1 hVQ (bV (mem_Lbar_of_pair H ht hh)) u = 0 ∧ Q u = 1) ∧
      LmodN S g t = pointRadical Q (aV ht) ∧
      LhmodN S g t h = pointRadical Q (bV (mem_Lbar_of_pair H ht hh)) ∧
      ((R0bar S g h).subgroupOf (Rbar S g t)).map (resV H.conj_mem t) = omegaGroup Q hQ := by
  have hth := mem_Lbar_of_pair H ht hh
  set β := beta H C ht ht1 hVQ with hβdef
  have hβa : β.IsAlt := beta_isAlt H C ht ht1 hVQ
  have hnd : β.Nondegenerate := beta_nondegenerate H C ht ht1 hVQ
  have h4 := hA.finrank_eq
  have hab := beta_aV_bV H C ht ht1 hVQ hh hb
  obtain ⟨u₁, u₂, h1a, h1b, h2a, h2b, h12⟩ := exists_hyperbolic_complement hβa hnd h4 hab
  set Q := qMinus β (aV ht) (bV hth) u₁ u₂ with hQdef
  have hpol : ∀ x y, polar Q x y = β x y := polar_qMinus hβa hnd h4 hab h1a h1b h2a h2b h12
  have hQnd := qMinus_nondegenerate hβa hnd h4 hab h1a h1b h2a h2b h12
  have hQa : Q (aV ht) = 0 := qMinus_a hβa h1a h2a
  have hQb : Q (bV hth) = 0 := qMinus_b hβa h1b h2b
  have hEa : LmodN S g t = pointRadical Q (aV ht) :=
    eq_pointRadical_of_index_two hβa hnd hpol hQnd (aV_ne_zero H ht) hQa
      (fun d hd => qMinus_eq_zero_iff_a hβa hnd h4 hab h1a h1b h2a h2b h12 hd)
      (LmodN_le_spPointRadical H C ht ht1 hVQ) (card_spPointRadical_eq_two_mul_a6 H C ht ht1 hVQ hA)
      hA.tau_not_mem hA.no_typeA
  obtain ⟨hLU, hLc, hLτ, hLno⟩ := LhmodN_props_a6 H C ht ht1 hVQ hA hh
  have hEb : LhmodN S g t h = pointRadical Q (bV hth) :=
    eq_pointRadical_of_index_two hβa hnd hpol hQnd (bV_ne_zero H hth) hQb
      (fun d hd => qMinus_eq_zero_iff_b hβa hnd h4 hab h1a h1b h2a h2b h12 hd) hLU hLc hLτ hLno
  refine ⟨Q, hQnd, polarBilin_qMinus hβa hnd h4 hab h1a h1b h2a h2b h12, hQa, hQb,
    ⟨u₁, h1a, h1b, qMinus_u₁ hβa h1b h12⟩, hEa, hEb, ?_⟩
  have himg : ((R0bar S g h).subgroupOf (Rbar S g t)).map (resV H.conj_mem t) =
      LmodN S g t ⊔ LhmodN S g t h := by
    rw [R0bar, subgroupOf_sup (Lbar_le_Rbar ht) (Lbar_mul_le_Rbar hth), Subgroup.map_sup,
      map_subgroupOf_resV H.conj_mem ht, map_subgroupOf_resV_mul H.conj_mem hth]
  rw [himg, hEa, hEb, ← S2.omegaFix_bot hQnd, ← S2.radFix_bot, ← S2.radFix_bot,
    S2.omegaFix_eq_closure_radFix hQnd (bot_inf_eq _) (m := 2) le_rfl
      (by rw [S2.perp_bot, finrank_top, h4]) (by rw [S2.perp_bot]; exact Submodule.mem_top)
      (by rw [S2.perp_bot]; exact Submodule.mem_top) (aV_ne_zero H ht) hQa hQb
      (by rw [hpol]; exact hab),
    Subgroup.closure_union, closure_eq, closure_eq]

end Pair

end A6

end CFSG.LargeExtraspecial.S6
