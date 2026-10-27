module

public import CFSG.LargeExtraspecial.S6OneB
public import CFSG.LargeExtraspecial.S2OrthMinus
public import CFSG.LargeExtraspecial.S6One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_wv (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) + 2 * finrank (ZMod 2) (Vt S g t) =
      2 * S.width := by
  have h1 := S2.finrank_map_add_finrank_inf_ker (Vt S g t).mkQ (Wt S g t)
  rw [Submodule.ker_mkQ, inf_eq_right.mpr (Vt_le_Wt H ht1)] at h1
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

section Two

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
  (hX : RmodN S g t = omegaGroup Q hQ) (hE : LmodN S g t = pointRadical Q (aV ht))
include hCE H hNo C ht ht1 hVQ hΩ hh hb hX hE

theorem timmesfeld_6_1_two :
    ∃ ρ : omegaGroup Q hQ →*
        (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)),
      (∀ (e : omegaGroup Q hQ) (x : Rbar S g t),
        (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
        ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
          ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
            (Vt S g t).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) ∧
      S2.RadDecomp ρ ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) := by
  have hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t :=
    fun x hx w hw => timmesfeld_6_1_one H C ht ht1 hVQ hh hb hCE hNo hΩ hx hw
  have hPI := pairInt_of_radBound H C ht ht1 hVQ (radBound_of_omegaCase H C ht ht1 hVQ hΩ)
  refine ⟨wvRep S g H t hN hX, fun e x hex w hw => wvRep_apply H hN hX hex hw, ?_⟩
  have hc := isCompl_fixOf_wvRep H hNo C ht ht1 hVQ hh hb hPI hN hX
  rw [hE, LhmodN_eq_pointRadical H ht hh (mem_Lbar_of_pair H ht hh) hX hE] at hc
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot, top_inf_eq, top_inf_eq]
  exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩

theorem timmesfeld_6_1_two_dvd (hQa : Q (aV ht) = 0)
    (hpol : polar Q (aV ht) (bV (mem_Lbar_of_pair H ht hh)) = 1) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) (Vt S g t) = 2 * m) :
    2 ^ (m - 1) ∣ finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) := by
  obtain ⟨ρ, -, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ hh hb hX hE
  have hth := mem_Lbar_of_pair H ht hh
  have heR : resV H.conj_mem t ⟨S.ρ h, hh⟩ ∈ omegaGroup Q hQ := by
    rw [← hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have hQb : Q (bV hth) = 0 := by
    rw [← resV_aV H.conj_mem ht hh hth,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp heR).1, hQa]
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot, top_inf_eq, top_inf_eq] at hD
  exact S2.timmesfeld_2_1_b_dvd_omega ρ hm hdim (aV_ne_zero H ht) hQa hQb hpol
    ⟨disjoint_iff.mpr hD.2, codisjoint_iff.mpr hD.1⟩

theorem timmesfeld_6_1_two_dvd_minus (hQa : Q (aV ht) = 0)
    (hpol : polar Q (aV ht) (bV (mem_Lbar_of_pair H ht hh)) = 1) {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) (Vt S g t) = 2 * m)
    (hmin : ∀ T : Submodule (ZMod 2) (Vt S g t), (∀ x ∈ T, Q x = 0) → finrank (ZMod 2) T < m) :
    2 ^ m ∣ finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) := by
  obtain ⟨ρ, -, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ hh hb hX hE
  have hth := mem_Lbar_of_pair H ht hh
  have heR : resV H.conj_mem t ⟨S.ρ h, hh⟩ ∈ omegaGroup Q hQ := by
    rw [← hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have hQb : Q (bV hth) = 0 := by
    rw [← resV_aV H.conj_mem ht hh hth,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp heR).1, hQa]
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot, top_inf_eq, top_inf_eq] at hD
  exact S2.timmesfeld_2_1_b_dvd_minus_omega ρ hm hdim hmin (aV_ne_zero H ht) hQa hQb hpol
    ⟨disjoint_iff.mpr hD.2, codisjoint_iff.mpr hD.1⟩

end Two

theorem beta_aV_bV (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    beta H C ht ht1 hVQ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) = 1 := by
  rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (aV ht) (bV (mem_Lbar_of_pair H ht hh)))
    with h0 | h1
  · exact absurd ((beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp h0) (cl_b_not_mem H hb)
  · exact h1

theorem timmesfeld_6_1_three (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ) :
    (∀ v : S.Qt, ((chi H C ht ht1 hVQ (Submodule.Quotient.mk v) : Vt S g t) : S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) ∧
    (∀ (x : Rbar S g t) (v : S.Qt),
      chi H C ht ht1 hVQ (Submodule.Quotient.mk (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
        resV H.conj_mem t x (chi H C ht ht1 hVQ (Submodule.Quotient.mk v))) ∧
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate),
      Q.polarBilin = beta H C ht ht1 hVQ ∧ RmodN S g t = omegaGroup Q hQ ∧
        LmodN S g t = pointRadical Q (aV ht) ∧
        ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)) :=
  ⟨coe_chi_apply_mk H C ht ht1 hVQ, chi_equivariant H C ht ht1 hVQ, hΩ.exists_form⟩

end CFSG.LargeExtraspecial.S6
