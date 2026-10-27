module

public import CFSG.LargeExtraspecial.S9Fus
public import CFSG.LargeExtraspecial.S9Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Fus

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

omit hCE hNo in
theorem inf_le_commSpace {h : S.M} {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (haV : S.cl (g * S.z * g⁻¹) ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    {p v₁ : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g)) (hv₁ : v₁ ∈ Vone S g t g ((h : G) * g))
    (hv₁P : v₁ ∉ S.clSub (S.QG ⊓ S.Qa g))
    (hpv : p + v₁ ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t ≤ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  intro d hd
  rw [Vone_eq_sup_inf] at hv₁
  obtain ⟨v, hv, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv₁
  have hvP : v ∉ S.clSub (S.QG ⊓ S.Qa g) := fun hvP => hv₁P (add_mem hvP hw₁.1)
  have hβv : beta H C ht ht1 hVQ (aV ht) ⟨v, hv⟩ = 1 := by
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (aV ht) ⟨v, hv⟩) with h0 | h0
    · exact absurd ((beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp h0) hvP
    · exact h0
  have hβd : beta H C ht ht1 hVQ (aV ht) ⟨d, hd.2⟩ = 0 :=
    (beta_aV_eq_zero_iff H C ht ht1 hVQ _).mpr hd.1
  have hρ : spRho (beta_isAlt H C ht ht1 hVQ) hβd 0 ∈ LmodN S g t := by
    rw [hSp.LmodN_eq]
    exact spRho_mem_spPointRadical _ hβd 0
  obtain ⟨l, hl, hle⟩ := hρ
  have hlv : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
      d + beta H C ht ht1 hVQ ⟨v, hv⟩ ⟨d, hd.2⟩ • S.cl (g * S.z * g⁻¹) := by
    have h1 := hle ⟨v, hv⟩
    rw [spRho_apply, beta_symm H C ht ht1 hVQ ⟨v, hv⟩ (aV ht), hβv] at h1
    simp only [one_smul, zero_mul, add_zero, Submodule.coe_add, Submodule.coe_smul] at h1
    rw [← h1]
    abel
  have hsp : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro w hw
    have h1 := Lbar_apply_sub_mem_span' haQ hw hl
    rcases mem_span_cl_iff.mp h1 with h0 | h0
    · rw [h0]
      exact zero_mem _
    · rw [h0]
      exact haV
  have hlu : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + (v + w₁)) - (p + (v + w₁)) ∈
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    sub_mem (S6.apply_mem_commSpace_of_commute (Lbar_comm S haQ hl hτL) hpv) hpv
  have e : d = ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + (v + w₁)) - (p + (v + w₁))) -
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) - ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) -
      beta H C ht ht1 hVQ ⟨v, hv⟩ ⟨d, hd.2⟩ • S.cl (g * S.z * g⁻¹) := by
    have : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + (v + w₁)) - (p + (v + w₁)) =
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) +
          ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) := by
      rw [map_add, map_add]
      abel
    rw [this, hlv]
    abel
  rw [e]
  exact sub_mem (sub_mem (sub_mem hlu (hsp p hp)) (hsp w₁ hw₁.1))
    (Submodule.smul_mem _ _ haV)

theorem false_of_commute_Nbar {x : S.O} (hxM : x ∈ S.Mbar)
    (hτA : x * t * x⁻¹ ∈ S.Lbar g ⊓ Nbar S g t) (hτt : x * t * x⁻¹ ≠ t)
    (hcN : ∀ n ∈ Nbar S g t, n * (x * t * x⁻¹) = x * t * x⁻¹ * n) : False := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hτ1 : x * t * x⁻¹ ≠ 1 := fun h1 => ht1 (by
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  have haV : S.cl (g * S.z * g⁻¹) ∈ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    by_contra hna
    apply hτ1
    refine C.faithful _ hτA.1 fun v hv => ?_
    rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' haQ hv hτA.1) with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (h0 ▸ sub_mem_commSpace _ v) hna
  obtain ⟨u, hu, huP⟩ : ∃ u ∈ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      u ∉ S.clSub (S.QG ⊓ S.Qa g) := by
    by_contra hcon
    push Not at hcon
    exact hτ1 (C.faithful _ hτA.1 (fix_of_commSpace_le_isotropic
      (fun u hu v hv => polar_eq_zero_of_mem_clSub H.conj_ne hu hv) hcon))
  obtain ⟨p, hp, v₁, hv₁, hv₁P, hpv⟩ :=
    exists_add_mem_commSpace hCE H C ht ht1 hVQ hSp hh hb hNo hτA.2 hcN hu huP
  have hsub := inf_le_commSpace H C ht ht1 hVQ hSp hτA.1 haV hp hv₁ hv₁P hpv
  obtain ⟨α, β', hα, hβ', hαβ⟩ := exists_hyperbolic_perp (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (four_le_finrank_Vt H C ht ht1 hVQ hNo)
    (aV_ne_zero H ht)
  have hαP := (beta_aV_eq_zero_iff H C ht ht1 hVQ α).mp hα
  have hβP := (beta_aV_eq_zero_iff H C ht ht1 hVQ β').mp hβ'
  have hα0 : (α : S.Qt) ≠ 0 := fun h0 => by
    rw [show α = 0 from Subtype.ext h0, map_zero, LinearMap.zero_apply] at hαβ
    exact zero_ne_one hαβ
  have hβ0 : (β' : S.Qt) ≠ 0 := fun h0 => by
    rw [show β' = 0 from Subtype.ext h0, map_zero] at hαβ
    exact zero_ne_one hαβ
  obtain ⟨kα, hkα, hkαe⟩ := exists_of_mem_orbit
    (mem_orbit_of_ne_zero ht hSp.transitive α.2 hα0) haQ
  obtain ⟨kβ, hkβ, hkβe⟩ := exists_of_mem_orbit
    (mem_orbit_of_ne_zero ht hSp.transitive β'.2 hβ0) haQ
  have hτα : x * t * x⁻¹ ∈ S.Lbar ((kα : G) * g) :=
    mem_Lbar_of_mem_commSpace H C ht ht1 hVQ hSp.transitive hxM (hkαe ▸ hsub ⟨hαP, α.2⟩)
  have hτβ : x * t * x⁻¹ ∈ S.Lbar ((kβ : G) * g) :=
    mem_Lbar_of_mem_commSpace H C ht ht1 hVQ hSp.transitive hxM (hkβe ▸ hsub ⟨hβP, β'.2⟩)
  have hkβQ := conj_mem_QG' S kβ.2 haQ
  have hαβQ : (kβ : G) * g * S.z * ((kβ : G) * g)⁻¹ ∉ S.Qa ((kα : G) * g) := by
    intro hmem
    have h1 := S.cl_mem_clSub (Subgroup.mem_inf.mpr ⟨hkβQ, hmem⟩) hkβQ
    have htkα := mem_Lbar_mul_of_mem_Rbar H ht hkα
    have e1 : bV htkα = α := Subtype.ext (by rw [coe_bV, ← hkαe])
    have hkβV : S.cl ((kβ : G) * g * S.z * ((kβ : G) * g)⁻¹) ∈ Vt S g t := by
      rw [← hkβe]
      exact β'.2
    have e2 : (⟨S.cl ((kβ : G) * g * S.z * ((kβ : G) * g)⁻¹), hkβV⟩ : Vt S g t) = β' :=
      Subtype.ext hkβe.symm
    have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hkα htkα ⟨_, hkβV⟩).mpr h1
    rw [e1, e2, hαβ] at h2
    exact one_ne_zero h2
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp kα kβ hkα hkβ hαβQ
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hR := (timmesfeld_6_5_N H ht hkα hkβ hgen hN0).2
  have hle : S.Lbar ((kα : G) * g) ⊔ S.Lbar ((kβ : G) * g) ≤
      centralizer ({x * t * x⁻¹} : Set S.O) := by
    refine sup_le (fun l hl => mem_centralizer_singleton_iff.mpr ?_)
      (fun l hl => mem_centralizer_singleton_iff.mpr ?_)
    · exact Lbar_comm S (conj_mem_QG' S kα.2 haQ) hl hτα
    · exact Lbar_comm S hkβQ hl hτβ
  have hc : ∀ y ∈ Rbar S g t, y * (x * t * x⁻¹) = x * t * x⁻¹ * y := by
    intro y hy
    rw [hR] at hy
    exact mem_centralizer_singleton_iff.mp (hle hy)
  rcases eq_one_or_eq_of_central H C ht ht1 hVQ hτA.1 hc with h1 | h1
  · exact hτ1 h1
  · exact hτt h1

theorem exists_conj_eq_mul_t {x : S.O} (hxM : x ∈ S.Mbar)
    (hτA : x * t * x⁻¹ ∈ S.Lbar g ⊓ Nbar S g t) (hτt : x * t * x⁻¹ ≠ t) :
    ∃ n ∈ Nbar S g t, n * (x * t * x⁻¹) * n⁻¹ = x * t * x⁻¹ * t := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  by_contra hcon
  push Not at hcon
  refine false_of_commute_Nbar hCE H hNo C ht ht1 hVQ hSp hxM hτA hτt fun n hn => ?_
  have h1 := hNQ.comm n hn _ hτA.2
  rcases S8.eq_one_or_eq_of_mem_zpowers htt h1 with h2 | h2
  · calc n * (x * t * x⁻¹) = (n * (x * t * x⁻¹) * n⁻¹ * (x * t * x⁻¹)⁻¹) *
        ((x * t * x⁻¹) * n) := by group
      _ = x * t * x⁻¹ * n := by rw [h2, one_mul]
  · exfalso
    apply hcon n hn
    have hτtc : x * t * x⁻¹ * t = t * (x * t * x⁻¹) :=
      commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hτA.2)
    calc n * (x * t * x⁻¹) * n⁻¹ = (n * (x * t * x⁻¹) * n⁻¹ * (x * t * x⁻¹)⁻¹) *
        (x * t * x⁻¹) := by group
      _ = t * (x * t * x⁻¹) := by rw [h2]
      _ = x * t * x⁻¹ * t := hτtc.symm

end Fus

end CFSG.LargeExtraspecial.S9
