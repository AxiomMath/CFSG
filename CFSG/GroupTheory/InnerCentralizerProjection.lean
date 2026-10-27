module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG

open scoped commutatorElement Pointwise
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {Γ : Type*} [Group Γ]

theorem le_sup_centralizer_of_forall_mem_range_conj {X R : Subgroup Γ}
    (hRX : R ≤ Subgroup.normalizer (X : Set Γ))
    (h : ∀ (r : Γ) (hr : r ∈ R),
      X.normalizerMonoidHom ⟨r, hRX hr⟩ ∈ (MulAut.conj : ↥X →* MulAut ↥X).range) :
    R ≤ X ⊔ Subgroup.centralizer (X : Set Γ) := by
  intro r hr
  obtain ⟨x, hx⟩ := h r hr
  have hxinvr : (x : Γ)⁻¹ * r ∈ Subgroup.centralizer (X : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hconj : r * j * r⁻¹ = (x : Γ) * j * (x : Γ)⁻¹ := by
      have h1 := congrArg (fun f : MulAut ↥X => (f ⟨j, hj⟩ : ↥X)) hx
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using
        (congrArg Subtype.val h1).symm
    have h2 : (x : Γ)⁻¹ * r * j * ((x : Γ)⁻¹ * r)⁻¹ = j := by
      calc
        (x : Γ)⁻¹ * r * j * ((x : Γ)⁻¹ * r)⁻¹
            = (x : Γ)⁻¹ * (r * j * r⁻¹) * x := by group
        _ = (x : Γ)⁻¹ * ((x : Γ) * j * (x : Γ)⁻¹) * x := by rw [hconj]
        _ = j := by group
    have h3 : j * ((x : Γ)⁻¹ * r) = ((x : Γ)⁻¹ * r) * j := by
      have h4 := congrArg (fun t => t * ((x : Γ)⁻¹ * r)) h2
      simpa [mul_assoc] using h4.symm
    exact h3
  have hxr : (x : Γ) * ((x : Γ)⁻¹ * r) = r := by group
  rw [← hxr]
  exact Subgroup.mul_mem_sup x.2 hxinvr

theorem normalizerMonoidHom_mem_commutator {X R T : Subgroup Γ}
    (hRX : R ≤ Subgroup.normalizer (X : Set Γ)) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hRT : R ≤ ⁅R, T⁆) {r : Γ} (hr : r ∈ R) :
    X.normalizerMonoidHom ⟨r, hRX hr⟩ ∈ commutator (MulAut ↥X) := by
  let N := Subgroup.normalizer (X : Set Γ)
  let L : Subgroup Γ :=
    ((commutator (MulAut ↥X)).comap X.normalizerMonoidHom).map N.subtype
  have hle : ⁅R, T⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_map]
    have haN : a ∈ N := hRX ha
    have hbN : b ∈ N := hTX hb
    have hNmem : ⁅a, b⁆ ∈ N :=
      Subgroup.commutator_le_self N (Subgroup.commutator_mem_commutator haN hbN)
    refine ⟨⟨⁅a, b⁆, hNmem⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hcomm : (⟨⁅a, b⁆, hNmem⟩ : N) =
        ⁅(⟨a, hRX ha⟩ : N), (⟨b, hTX hb⟩ : N)⁆ := by
      ext
      rfl
    rw [hcomm, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hmem : r ∈ L := (hRT.trans hle) hr
  obtain ⟨n, hn, hnr⟩ := Subgroup.mem_map.mp hmem
  rw [Subgroup.mem_comap] at hn
  have hnr' : n = ⟨r, hRX hr⟩ := Subtype.ext hnr
  rwa [hnr'] at hn

theorem isPGroup_sup_centralizer_inf [Finite Γ] {p : ℕ} [Fact p.Prime] {J R : Subgroup Γ}
    (hRJ : R ≤ Subgroup.normalizer (J : Set Γ))
    (hJ : J ⊓ Subgroup.centralizer (J : Set Γ) = ⊥) (hR : IsPGroup p R) :
    IsPGroup p ↥((R ⊔ Subgroup.centralizer (J : Set Γ)) ⊓ J) := by
  let C := Subgroup.centralizer (J : Set Γ)
  let S := R ⊔ C
  have hRC : R ≤ Subgroup.normalizer (C : Set Γ) :=
    hRJ.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer J)
  have hJC : J ≤ Subgroup.normalizer (C : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro j hj c hc
    have hcomm : j * c = c * j := (Subgroup.mem_centralizer_iff.mp hc) j hj
    rwa [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  haveI hKnormal : (C.subgroupOf S).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hRC
  have hRsub : IsPGroup p (R.subgroupOf S) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe (show R ≤ S from le_sup_left)).symm
  have htop : R.subgroupOf S ⊔ C.subgroupOf S = ⊤ := by
    refine (Subgroup.eq_top_iff' (R.subgroupOf S ⊔ C.subgroupOf S)).mpr fun x => ?_
    have hx : (x : Γ) ∈ (R : Set Γ) * (C : Set Γ) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R C hRC]
      exact x.2
    obtain ⟨r, hr, c, hc, hrc⟩ := hx
    have hxeq : x = (⟨r, Subgroup.mem_sup_left hr⟩ : S) * ⟨c, Subgroup.mem_sup_right hc⟩ := by
      ext
      exact hrc.symm
    rw [hxeq]
    exact Subgroup.mul_mem_sup (show (⟨r, Subgroup.mem_sup_left hr⟩ : S) ∈ R.subgroupOf S from hr)
      (show (⟨c, Subgroup.mem_sup_right hc⟩ : S) ∈ C.subgroupOf S from hc)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (C.subgroupOf S)).comp (Subgroup.subtype (R.subgroupOf S))) := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf S) y
    have hs : s ∈ R.subgroupOf S ⊔ C.subgroupOf S := by
      rw [htop]
      exact Subgroup.mem_top s
    rw [Subgroup.mem_sup_of_normal_right] at hs
    obtain ⟨r, hr, c, hc, hrc⟩ := hs
    refine ⟨⟨r, hr⟩, ?_⟩
    change (QuotientGroup.mk' (C.subgroupOf S)) (r : S) =
      (QuotientGroup.mk' (C.subgroupOf S)) s
    have hc1 : (QuotientGroup.mk' (C.subgroupOf S)) c = 1 :=
      (QuotientGroup.eq_one_iff c).mpr hc
    rw [← hrc, map_mul, hc1, mul_one]
  have hQuot : IsPGroup p (S ⧸ C.subgroupOf S) :=
    hRsub.of_surjective ((QuotientGroup.mk' (C.subgroupOf S)).comp
      (Subgroup.subtype (R.subgroupOf S))) hsurj
  let g : ↥(S ⊓ J) →* S ⧸ C.subgroupOf S :=
    (QuotientGroup.mk' (C.subgroupOf S)).comp (Subgroup.inclusion inf_le_left)
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 : (⟨x.1, x.2.1⟩ : S)⁻¹ * ⟨y.1, y.2.1⟩ ∈ C.subgroupOf S := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (C.subgroupOf S)) ((⟨x.1, x.2.1⟩ : S)⁻¹ *
        ⟨y.1, y.2.1⟩) = 1
      rw [map_mul, map_inv]
      change (g x)⁻¹ * g y = 1
      rw [hxy, inv_mul_cancel]
    have h2 : (x : Γ)⁻¹ * (y : Γ) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : (x : Γ)⁻¹ * (y : Γ) ∈ J :=
      J.mul_mem (J.inv_mem x.2.2) y.2.2
    have h4 : (x : Γ)⁻¹ * (y : Γ) = 1 := by
      have h5 : (x : Γ)⁻¹ * (y : Γ) ∈ J ⊓ C := ⟨h3, h2⟩
      rwa [hJ, Subgroup.mem_bot] at h5
    refine Subtype.ext ?_
    have h5 := congrArg (fun t => (x : Γ) * t) h4
    simpa [mul_assoc] using h5.symm
  exact hQuot.of_injective g hginj

theorem sup_centralizer_inf_ne_bot {J R : Subgroup Γ} (hRJ : R ≤ Subgroup.normalizer (J : Set Γ))
    (hRle : R ≤ J ⊔ Subgroup.centralizer (J : Set Γ))
    (hRC : R ⊓ Subgroup.centralizer (J : Set Γ) = ⊥) (hR : R ≠ ⊥) :
    (R ⊔ Subgroup.centralizer (J : Set Γ)) ⊓ J ≠ ⊥ := by
  let C := Subgroup.centralizer (J : Set Γ)
  have hJC : J ≤ Subgroup.normalizer (C : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    intro j hj c hc
    have hcomm : j * c = c * j := (Subgroup.mem_centralizer_iff.mp hc) j hj
    rwa [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨r, hrne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hr : (r : Γ) ∈ R := r.2
  have hr1 : (r : Γ) ≠ 1 := fun h => hrne (Subtype.ext h)
  have hmem : (r : Γ) ∈ (J : Set Γ) * (C : Set Γ) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J C hJC]
    exact hRle hr
  obtain ⟨j, hj, c, hc, hjc⟩ := hmem
  have hjS : j ∈ R ⊔ C := by
    have hjeq : j = (r : Γ) * c⁻¹ := by
      rw [← hjc]
      group
    rw [hjeq]
    exact Subgroup.mul_mem_sup hr (C.inv_mem hc)
  have hjne : j ≠ 1 := by
    intro hj1
    apply hr1
    have hrc_eq : (r : Γ) = c := by
      calc
        (r : Γ) = j * c := hjc.symm
        _ = 1 * c := by rw [hj1]
        _ = c := one_mul c
    have hrc : (r : Γ) ∈ C := by
      rwa [hrc_eq]
    have hmem : (r : Γ) ∈ R ⊓ C := ⟨hr, hrc⟩
    rwa [hRC, Subgroup.mem_bot] at hmem
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨j, ⟨hjS, hj⟩⟩, ?_⟩
  intro h
  exact hjne (congrArg Subtype.val h)

theorem normalizer_inf_le_normalizer_sup_centralizer_inf {J R : Subgroup Γ} :
    Subgroup.normalizer (R : Set Γ) ⊓ Subgroup.normalizer (J : Set Γ) ≤
      Subgroup.normalizer (((R ⊔ Subgroup.centralizer (J : Set Γ)) ⊓ J : Subgroup Γ) : Set Γ) := by
  let C := Subgroup.centralizer (J : Set Γ)
  have h1 : Subgroup.normalizer (R : Set Γ) ⊓ Subgroup.normalizer (J : Set Γ) ≤
      Subgroup.normalizer (C : Set Γ) :=
    inf_le_right.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer J)
  have h2 : Subgroup.normalizer (R : Set Γ) ⊓ Subgroup.normalizer (J : Set Γ) ≤
      Subgroup.normalizer ((R ⊔ C : Subgroup Γ) : Set Γ) :=
    (le_inf inf_le_left h1).trans (Subgroup.inf_normalizer_le_normalizer_sup R C)
  exact (le_inf h2 inf_le_right).trans
    (Subgroup.inf_normalizer_le_normalizer_inf (H := R ⊔ C) (K := J))

theorem mem_centralizer_of_commutator_mem_center {J : Subgroup Γ} (hJ : Group.IsPerfect ↥J)
    {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ))
    (hrJ : ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ (Subgroup.center ↥J).map J.subtype) :
    r ∈ Subgroup.centralizer (J : Set Γ) := by
  let σ : MulAut ↥J := J.normalizerMonoidHom ⟨r, hr⟩
  have hcommJ : ∀ j : ↥J, (σ j : ↥J) * j⁻¹ ∈ Subgroup.center ↥J := by
    intro j
    have hmem : (((σ j : ↥J) * j⁻¹ : ↥J) : Γ) ∈
        (Subgroup.center ↥J).map J.subtype := by
      simpa [σ, Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_inv]
        using hrJ (j : Γ) j.2
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
    have hz' : z = (σ j : ↥J) * j⁻¹ := Subtype.ext hzeq
    rwa [hz'] at hz
  have hquot : onCenterQuotient σ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) x
    rw [onCenterQuotient_apply_mk]
    exact (QuotientGroup.eq_iff_div_mem (x := σ j) (y := j)).mpr
      (by simpa [div_eq_mul_inv] using hcommJ j)
  have hσ : σ = 1 := onCenterQuotient_eq_one_imp σ hquot
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : r * j * r⁻¹ = j := by
    have h2 := congrArg (fun f : MulAut ↥J => (f ⟨j, hj⟩ : ↥J)) hσ
    simpa [σ, Subgroup.normalizerMonoidHom_apply_apply_coe] using congrArg Subtype.val h2
  calc
    j * r = (r * j * r⁻¹) * r := by rw [h1]
    _ = r * j := by group

theorem mem_centralizer_of_commutator_mem_of_isQuasisimple {J K : Subgroup Γ}
    (hJ : IsQuasisimple ↥J) (hJK : J ≤ Subgroup.normalizer (K : Set Γ)) (hJK' : ¬ J ≤ K)
    {r : Γ} (hr : r ∈ Subgroup.normalizer (J : Set Γ))
    (hrJ : ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ K) :
    r ∈ Subgroup.centralizer (J : Set Γ) := by
  have hNnormal : ((J ⊓ K).subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((le_inf J.le_normalizer hJK).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hNne : (J ⊓ K).subgroupOf J ≠ ⊤ := by
    intro htop
    exact hJK' ((Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right)
  have hcenter : (J ⊓ K).subgroupOf J ≤ Subgroup.center ↥J := by
    rcases LocalCores.quasisimple_normal_subgroups hJ hNnormal with htop | hle
    · exact absurd htop hNne
    · exact hle
  refine mem_centralizer_of_commutator_mem_center hJ.1 hr ?_
  intro j hj
  have hjmem : r * j * r⁻¹ * j⁻¹ ∈ J := by
    have hconj : r * j * r⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hr j).mp hj
    exact J.mul_mem hconj (J.inv_mem hj)
  have hmem : (⟨r * j * r⁻¹ * j⁻¹, hjmem⟩ : ↥J) ∈ (J ⊓ K).subgroupOf J :=
    ⟨hjmem, hrJ j hj⟩
  have hz : (⟨r * j * r⁻¹ * j⁻¹, hjmem⟩ : ↥J) ∈ Subgroup.center ↥J := hcenter hmem
  exact Subgroup.mem_map_of_mem J.subtype hz

end CFSG

end
