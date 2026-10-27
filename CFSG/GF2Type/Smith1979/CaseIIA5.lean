module

public import CFSG.GF2Type.Smith1979.CaseIIA4
public import CFSG.LargeExtraspecial.S11Basic
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem resR_eq_one_iff (r : Rbar S g t) : D.resR r = 1 ↔ (r : S.O) = 1 ∨ (r : S.O) = t := by
  constructor
  · intro h
    have hfix := (resCt_eq_one_iff
      (⟨(r : S.O), Rbar_le_centralizer D.H.conj_mem r.2⟩ : ↥(centralizer ({t} : Set S.O)))).mp h
    exact D.eq_one_or_eq_t_of_K (Rbar_le_Mbar r.2)
      ⟨commute_of_mem_Rbar D.H.conj_mem r.2, hfix⟩
  · rintro (h | h)
    · have : r = 1 := Subtype.ext h
      rw [this, map_one]
    · exact (resCt_eq_one_iff
        (⟨(r : S.O), Rbar_le_centralizer D.H.conj_mem r.2⟩ :
          ↥(centralizer ({t} : Set S.O)))).mpr fun u hu => by
        rw [h]
        exact D.isK_t.fix u hu

@[expose] noncomputable def resN : Nbar S g t →*
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  D.resR.comp (Subgroup.inclusion Nbar_le_Rbar)

@[expose] noncomputable def Gam0 : Subgroup
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  D.resN.range

theorem Nbar_eq_N0bar (hCE : S4.CentralExtInput.{u}) : Nbar S g t = N0bar S g t := by
  have hR : Rbar S g t ≠ S.Lbar g := by
    intro hR
    have h1 := Submodule.finrank_mono (S11.Vt_le_span_of_Rbar_eq D.H D.C hR)
    have h2 := finrank_span_singleton (K := ZMod 2)
      (cl_conj_z_ne_zero S D.H.conj_mem D.H.conj_ne)
    have := D.h3
    omega
  rcases timmesfeld_4_7_a hCE D.H D.hNo D.C D.ht D.ht1 hR
      (fun hVQ => absurd D.hL.le_Qa hVQ) with ⟨-, h, -⟩ | ⟨hA, -⟩
  · exact h
  · exact absurd hA.1 (by rw [D.h3]; norm_num)

theorem Gam0_le_Alt (hCE : S4.CentralExtInput.{u}) :
    D.Gam0 ≤ Sp.AltGrp (omegaU t) (Vsub g t) D.spData := by
  let P : Subgroup S.O :=
    ((Sp.AltGrp (omegaU t) (Vsub g t) D.spData).comap D.resR).map (Rbar S g t).subtype
  have hN : Nbar S g t ≤ P := by
    rw [D.Nbar_eq_N0bar hCE]
    refine iSup₂_le fun k hk => ?_
    rintro x ⟨hxL, hxN⟩
    have hxR : x ∈ Rbar S g t := Nbar_le_Rbar hxN
    rw [Lbar_mul S k g] at hxL
    obtain ⟨l, hl, hxe⟩ := hxL
    have hxe' : S.ρ k * l * (S.ρ k)⁻¹ = x := hxe
    have hρk : S.ρ k * t = t * S.ρ k := commute_of_mem_Rbar D.H.conj_mem hk
    have hρk' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
      rw [map_inv]
      exact commute_of_mem_Rbar D.H.conj_mem (inv_mem hk)
    have hlN : l ∈ Nbar S g t := by
      have h1 := conj_mem_Nbar D.H.conj_mem hρk' hxN
      have h2 : S.ρ k⁻¹ * x * (S.ρ k⁻¹)⁻¹ = l := by
        rw [map_inv, ← hxe']
        group
      rwa [h2] at h1
    set r0 : Rbar S g t := ⟨S.ρ k, hk⟩ with hr0
    set l' : Rbar S g t := ⟨l, Lbar_le_Rbar D.ht hl⟩ with hl'
    have hlΛ : D.resR l' ∈ D.Lam := D.mem_Lam.mpr ⟨l, hl, rfl⟩
    have hVtriv : ∀ v ∈ Vsub g t, D.resR l' v = v := by
      intro v hv
      apply Subtype.ext
      exact hlN.2 _ hv
    have hlAlt : D.resR l' ∈ Sp.AltGrp (omegaU t) (Vsub g t) D.spData :=
      ⟨⟨D.isGamma.isom _ ⟨l', rfl⟩, hVtriv⟩, fun u =>
        Sp.alt_of_Lambda D.spData D.isGamma D.aW_mem_Vsub D.aW_ne_zero D.Lam_le_Gam
          (fun x hx u hu => D.Lam_sub_mem_span hx u hu)
          (fun γ hγ hγa x hx => D.Lam_conj_mem hγ hγa hx)
          (fun x hx => D.Lam_not_transvection hx) hlΛ hVtriv u⟩
    have hconjAlt := Sp.AltGrp.conj_mem D.spData (γ := D.resR r0)
      (D.isGamma.isom _ ⟨r0, rfl⟩) (D.isGamma.stabV _ ⟨r0, rfl⟩) hlAlt
    have e1 : (⟨x, hxR⟩ : Rbar S g t) = r0 * l' * r0⁻¹ := Subtype.ext hxe'.symm
    have e2 : D.resR (r0 * l' * r0⁻¹) = D.resR r0 * D.resR l' * D.resR r0⁻¹ :=
      (map_mul D.resR _ _).trans (congrArg (fun y => y * D.resR r0⁻¹) (map_mul D.resR _ _))
    have e3 : D.resR r0⁻¹ = (D.resR r0)⁻¹ := map_inv D.resR r0
    have e4 : D.resR ⟨x, hxR⟩ = D.resR r0 * D.resR l' * (D.resR r0)⁻¹ :=
      (congrArg D.resR e1).trans
        (e2.trans (congrArg (fun y => D.resR r0 * D.resR l' * y) e3))
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    show D.resR ⟨x, hxR⟩ ∈ Sp.AltGrp (omegaU t) (Vsub g t) D.spData
    rw [e4]
    exact hconjAlt
  rintro _ ⟨n, rfl⟩
  obtain ⟨r, hr, hrn⟩ := hN n.2
  have : r = Subgroup.inclusion Nbar_le_Rbar n := Subtype.ext hrn
  show D.resR (Subgroup.inclusion Nbar_le_Rbar n) ∈ _
  rw [← this]
  exact hr

theorem card_Lbar_inf_Nbar : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) = 8 := by
  have h1 := card_Lbar_eq_mul D.H.conj_mem D.ht
  rw [D.C.card_Lbar, D.hw, D.hL.LmodN_eq, card_centreGroup (aV_ne_zero D.H D.ht), D.h3] at h1
  have e1 : (2 : ℕ) ^ (6 - 1) = 32 := by norm_num
  have e2 : (2 : ℕ) ^ (3 - 1) = 4 := by norm_num
  rw [e1, e2] at h1
  omega

theorem Gam0_conj {γ x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hγ : γ ∈ D.Gam) (hx : x ∈ D.Gam0) :
    γ * x * γ⁻¹ ∈ D.Gam0 := by
  obtain ⟨r, rfl⟩ := hγ
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar r.2)
  have hρk : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact commute_of_mem_Rbar D.H.conj_mem r.2
  have hmem : (r : S.O) * (n : S.O) * (r : S.O)⁻¹ ∈ Nbar S g t := by
    have := conj_mem_Nbar D.H.conj_mem hρk n.2
    rwa [hk] at this
  refine ⟨⟨_, hmem⟩, ?_⟩
  let n' : Rbar S g t := Subgroup.inclusion Nbar_le_Rbar n
  have e1 : (Subgroup.inclusion Nbar_le_Rbar (⟨_, hmem⟩ : Nbar S g t) : Rbar S g t) =
      r * n' * r⁻¹ := Subtype.ext rfl
  have e2 : D.resR (r * n' * r⁻¹) = D.resR r * D.resR n' * D.resR r⁻¹ :=
    (map_mul D.resR _ _).trans (congrArg (fun y => y * D.resR r⁻¹) (map_mul D.resR _ _))
  have e3 : D.resR r⁻¹ = (D.resR r)⁻¹ := map_inv D.resR r
  exact ((congrArg D.resR e1).trans
    (e2.trans (congrArg (fun y => D.resR r * D.resR n' * y) e3)))

theorem exists_Nbar_not_Lbar : ∃ n ∈ Nbar S g t, n ∉ S.Lbar g := by
  by_contra hcon
  push Not at hcon
  have hΛc : ∀ x ∈ D.Gam0, ∀ u, omegaU t u D.aW = 0 →
      x u - u ∈ Submodule.span (ZMod 2) {D.aW} := by
    rintro _ ⟨n, rfl⟩ u hu
    exact D.Lam_sub_mem_span (D.mem_Lam.mpr ⟨n.1, hcon n.1 n.2, rfl⟩) u hu
  have hbot : D.Gam0 = ⊥ := Sp.eq_bot_of_normal D.spData D.isGamma D.aW_mem_Vsub
    D.aW_ne_zero hΛc (fun γ hγ x hx => D.Gam0_conj hγ hx)
  have hle : S.Lbar g ⊓ Nbar S g t ≤ zpowers t := by
    intro n hn
    have h1 : D.resR (Subgroup.inclusion Nbar_le_Rbar ⟨n, hn.2⟩) = 1 := by
      have : D.resN ⟨n, hn.2⟩ ∈ D.Gam0 := ⟨_, rfl⟩
      rw [hbot] at this
      exact this
    rcases (D.resR_eq_one_iff _).mp h1 with h | h
    · have : n = 1 := h
      rw [this]
      exact one_mem _
    · have : n = t := h
      rw [this]
      exact mem_zpowers t
  have h2 := Subgroup.card_le_of_le hle
  have h3 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ D.ht1
    rw [_root_.sq]
    exact D.htt'
  have h4 := D.card_Lbar_inf_Nbar
  omega

@[expose] noncomputable def tN : Nbar S g t := ⟨t, self_mem_Nbar D.H D.ht⟩

theorem ker_resN : D.resN.ker = zpowers D.tN := by
  ext n
  rw [MonoidHom.mem_ker, mem_zpowers_iff]
  constructor
  · intro h
    rcases (D.resR_eq_one_iff _).mp h with h1 | h1
    · exact ⟨0, by rw [zpow_zero]; exact (Subtype.ext h1).symm⟩
    · exact ⟨1, by rw [zpow_one]; exact (Subtype.ext h1).symm⟩
  · rintro ⟨k, rfl⟩
    have htN : D.resN D.tN = 1 := (D.resR_eq_one_iff _).mpr (Or.inr rfl)
    rw [map_zpow, htN, one_zpow]

theorem card_ker_resN : Nat.card D.resN.ker = 2 := by
  rw [D.ker_resN, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · rw [_root_.sq]
    exact Subtype.ext D.htt'
  · intro h
    exact D.ht1 (congrArg Subtype.val h)

theorem card_Nbar_eq_two_mul : Nat.card (Nbar S g t) = 2 * Nat.card D.Gam0 := by
  have h := Subgroup.card_ker_mul_card_range D.resN
  rw [D.card_ker_resN] at h
  exact h.symm

theorem sixteen_le_card_Nbar (hCE : S4.CentralExtInput.{u}) : 16 ≤ Nat.card (Nbar S g t) := by
  obtain ⟨n, hnN, hnL⟩ := D.exists_Nbar_not_Lbar
  have hle : S.Lbar g ⊓ Nbar S g t ≤ Nbar S g t := inf_le_right
  have hdvd := Subgroup.card_dvd_of_le hle
  have hne : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≠ Nat.card (Nbar S g t) := by
    intro heq
    have h := Subgroup.eq_of_le_of_card_ge hle heq.ge
    have hmem : n ∈ S.Lbar g ⊓ Nbar S g t := by
      rw [h]
      exact hnN
    exact hnL hmem.1
  rw [D.card_Lbar_inf_Nbar] at hdvd hne
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card (Nbar S g t) := Nat.card_pos
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

theorem Gam0_eq_Alt (hCE : S4.CentralExtInput.{u}) :
    D.Gam0 = Sp.AltGrp (omegaU t) (Vsub g t) D.spData := by
  refine Sp.eq_alt_of_card D.spData (D.Gam0_le_Alt hCE) ?_
  have h1 := D.card_Nbar_eq_two_mul
  have h2 := D.sixteen_le_card_Nbar hCE
  omega

theorem card_Gam0 (hCE : S4.CentralExtInput.{u}) : Nat.card D.Gam0 = 8 := by
  have h1 := Sp.card_AltGrp_le D.spData
  have h2 := D.card_Nbar_eq_two_mul
  have h3 := D.sixteen_le_card_Nbar hCE
  rw [D.Gam0_eq_Alt hCE]
  rw [D.Gam0_eq_Alt hCE] at h2
  omega

theorem card_Nbar (hCE : S4.CentralExtInput.{u}) : Nat.card (Nbar S g t) = 16 := by
  have h1 := D.card_Nbar_eq_two_mul
  have h2 := D.card_Gam0 hCE
  omega

theorem card_GL_Vt : Nat.card (Vt S g t ≃ₗ[ZMod 2] Vt S g t) = 168 := by
  rw [CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod D.h3]
  simp [Fin.prod_univ_succ]

theorem card_Rbar (hCE : S4.CentralExtInput.{u}) : Nat.card (Rbar S g t) = 2688 := by
  have h := Subgroup.card_ker_mul_card_range (resV D.H.conj_mem t)
  have hker : (resV D.H.conj_mem t).ker = (Nbar S g t).subgroupOf (Rbar S g t) := by
    ext x
    rw [MonoidHom.mem_ker, resV_eq_one_iff, mem_subgroupOf]
  have hrange : (resV D.H.conj_mem t).range = ⊤ := by
    rw [range_resV, D.hL.eq_top]
  have hker_card : Nat.card ((Nbar S g t).subgroupOf (Rbar S g t)) = Nat.card (Nbar S g t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Nbar_le_Rbar).toEquiv
  rw [hker, hker_card, D.card_Nbar hCE, hrange, Subgroup.card_top, D.card_GL_Vt] at h
  omega

theorem Gam0_le_Gam : D.Gam0 ≤ D.Gam := by
  rintro _ ⟨n, rfl⟩
  exact ⟨Subgroup.inclusion Nbar_le_Rbar n, rfl⟩

theorem centralizer_inf_Mbar_eq (hCE : S4.CentralExtInput.{u}) :
    centralizer ({t} : Set S.O) ⊓ S.Mbar = Rbar S g t := by
  refine le_antisymm ?_ (le_inf (Rbar_le_centralizer D.H.conj_mem) Rbar_le_Mbar)
  rintro c ⟨hcC, hcM⟩
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hcM
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hcC
  have hρk : S.ρ k * t = t * S.ρ k := by rw [hk]; exact hct
  set cc : ↥(centralizer ({t} : Set S.O)) := ⟨c, hcC⟩ with hcc
  have hy : ∀ u v, omegaU t (resCt t cc u) (resCt t cc v) = omegaU t u v :=
    fun u v => D.omegaU_resCt cc u v
  have hyV : ∀ v ∈ Vsub g t, resCt t cc v ∈ Vsub g t := by
    intro v hv
    change (((resCt t cc v : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt)) ∈ Vt S g t
    rw [coe_resCt]
    have := apply_mem_Vt D.H.conj_mem hρk hv
    rwa [hk] at this
  have hyN : ∀ γ ∈ D.Gam, resCt t cc * γ * (resCt t cc)⁻¹ ∈ D.Gam := by
    rintro _ ⟨r, rfl⟩
    have hmem : c * (r : S.O) * c⁻¹ ∈ Rbar S g t := by
      have := conj_mem_Rbar hρk r.2
      rwa [hk] at this
    refine ⟨⟨_, hmem⟩, ?_⟩
    let r' : ↥(centralizer ({t} : Set S.O)) :=
      ⟨(r : S.O), Rbar_le_centralizer D.H.conj_mem r.2⟩
    have e1 : (⟨c * (r : S.O) * c⁻¹, Rbar_le_centralizer D.H.conj_mem hmem⟩ :
        ↥(centralizer ({t} : Set S.O))) = cc * r' * cc⁻¹ := Subtype.ext rfl
    have e2 : resCt t (cc * r' * cc⁻¹) = resCt t cc * resCt t r' * resCt t cc⁻¹ :=
      (map_mul (resCt t) _ _).trans
        (congrArg (fun y => y * resCt t cc⁻¹) (map_mul (resCt t) _ _))
    have e3 : resCt t cc⁻¹ = (resCt t cc)⁻¹ := map_inv (resCt t) cc
    exact (congrArg (resCt t) e1).trans
      (e2.trans (congrArg (fun y => resCt t cc * resCt t r' * y) e3)).symm
  have hΓ0 : ∀ γ ∈ D.Gam, Sp.IsF (omegaU t) (Vsub g t) γ → ∀ u,
      omegaU t (γ u - u) u = 0 := by
    rintro _ ⟨r, rfl⟩ hF u
    have hrN : (r : S.O) ∈ Nbar S g t := by
      refine ⟨r.2, fun v hv => ?_⟩
      have h1 := hF.triv ⟨v, Vt_le_commSpace D.H D.ht1 hv⟩ hv
      exact congrArg Subtype.val h1
    exact (D.Gam0_le_Alt hCE ⟨⟨r, hrN⟩, rfl⟩).2 u
  have hAlt : ∀ x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), Sp.IsF (omegaU t) (Vsub g t) x →
      (∀ u, omegaU t (x u - u) u = 0) → x ∈ D.Gam := by
    intro x hF halt
    have : x ∈ Sp.AltGrp (omegaU t) (Vsub g t) D.spData := ⟨hF, halt⟩
    rw [← D.Gam0_eq_Alt hCE] at this
    exact D.Gam0_le_Gam this
  obtain ⟨r, hr⟩ := Sp.IsGamma.mem_of_normalizes D.spData D.isGamma hΓ0 hAlt hy hyV hyN
  have hrc : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
    intro u hu
    have := congrArg (fun e => ((e ⟨u, hu⟩ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt)) hr
    exact this
  have hc' : c⁻¹ * t = t * c⁻¹ :=
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
      _ = t * c⁻¹ := by group
  have hr' : (r : S.O) * t = t * (r : S.O) := commute_of_mem_Rbar D.H.conj_mem r.2
  have hK : IsK t (c⁻¹ * (r : S.O)) := by
    refine ⟨?_, fun u hu => ?_⟩
    · calc c⁻¹ * (r : S.O) * t = c⁻¹ * ((r : S.O) * t) := by rw [mul_assoc]
        _ = c⁻¹ * (t * (r : S.O)) := by rw [hr']
        _ = (c⁻¹ * t) * (r : S.O) := by rw [mul_assoc]
        _ = (t * c⁻¹) * (r : S.O) := by rw [hc']
        _ = t * (c⁻¹ * (r : S.O)) := by rw [mul_assoc]
    · rw [coe_mul_apply, hrc u hu]
      exact inv_apply_apply_O c u
  have hk0 : c⁻¹ * (r : S.O) ∈ S.Mbar := mul_mem (inv_mem hcM) (Rbar_le_Mbar r.2)
  rcases D.eq_one_or_eq_t_of_K hk0 hK with h | h
  · have : c = (r : S.O) := inv_mul_eq_one.mp h
    rw [this]
    exact r.2
  · have hct' : c * t = (r : S.O) :=
      calc c * t = c * (c⁻¹ * (r : S.O)) := by rw [h]
        _ = (r : S.O) := by group
    have : c = (r : S.O) * t := by
      calc c = c * (t * t) := by rw [D.htt', mul_one]
        _ = (c * t) * t := by rw [mul_assoc]
        _ = (r : S.O) * t := by rw [hct']
    rw [this]
    exact mul_mem r.2 (Lbar_le_Rbar D.ht D.ht)

end Data

end CFSG.GF2Type.Smith1979.Case2
