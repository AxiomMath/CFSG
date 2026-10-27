module

public import CFSG.LargeExtraspecial.S8A5A
public import CFSG.LargeExtraspecial.S8CorBApply

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem exists_bilin_eq_of_additive {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.Nondegenerate)
    (f : V → ZMod 2) (hf : ∀ u v, f (u + v) = f u + f v) : ∃ w, ∀ v, B w v = f v := by
  set δ : V →ₗ[ZMod 2] ZMod 2 := AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' f hf)
  refine ⟨(B.toDual hB).symm δ, fun v => ?_⟩
  rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]
  rfl

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem beta_resCV (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (y : CMt S t) (u v : Vt S g t) :
    beta H C ht ht1 hVQ (resCV S g H.conj_mem t y u) (resCV S g H.conj_mem t y v) =
      beta H C ht ht1 hVQ u v := by
  obtain ⟨v', hv'⟩ := exists_t_sub_eq H C ht ht1 hVQ v
  have hyt : (y : S.O) * t = t * (y : S.O) := (mem_CMt.mp y.2).2
  have hv'' : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v') -
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v' = (resCV S g H.conj_mem t y v : S.Qt) := by
    rw [coe_resCV_apply, ← hv', map_sub, ← coe_mul_apply, ← coe_mul_apply, hyt]
  rw [beta_apply H C ht ht1 hVQ _ _ hv'', beta_apply H C ht ht1 hVQ _ _ hv', coe_resCV_apply,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (y : S.O).2]

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem Std.Q_resCV (D : Std H C ht ht1 hVQ) (y : CMt S t) (v : Vt S g t) :
    D.Q (resCV S g H.conj_mem t y v) = D.Q v := by
  have haQ := H.conj_mem
  have hβnd := beta_nondegenerate H C ht ht1 hVQ
  have hpolβ : ∀ u w : Vt S g t, polar D.Q u w = beta H C ht ht1 hVQ u w := fun u w => by
    rw [← polarBilin_apply_apply, D.hpol]
  have hQr : ∀ (r : Rbar S g t) (w : Vt S g t), D.Q (resV haQ t r w) = D.Q w := by
    intro r w
    have heR : resV haQ t r ∈ omegaGroup D.Q D.hQ := by
      rw [← D.hX, ← range_resV haQ t]; exact ⟨r, rfl⟩
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp heR).1 w
  set e := resCV S g haQ t y with he
  have hadd : ∀ u w : Vt S g t, D.Q (e (u + w)) + D.Q (u + w) =
      (D.Q (e u) + D.Q u) + (D.Q (e w) + D.Q w) := by
    intro u w
    rw [map_add, QuadraticMap.map_add D.Q (e u) (e w), QuadraticMap.map_add D.Q u w, hpolβ,
      hpolβ, he, beta_resCV]
    linear_combination zmod2_add_self (beta H C ht ht1 hVQ u w)
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (mem_CMt.mp y.2).1
  have hkt : S.ρ k * t = t * S.ρ k := by rw [hk]; exact (mem_CMt.mp y.2).2
  have hδr : ∀ (r : Rbar S g t) (w : Vt S g t),
      D.Q (e (resV haQ t r w)) + D.Q (resV haQ t r w) = D.Q (e w) + D.Q w := by
    intro r w
    have hr' : S.ρ k * (r : S.O) * (S.ρ k)⁻¹ ∈ Rbar S g t := conj_mem_Rbar hkt r.2
    have h1 : e (resV haQ t r w) = resV haQ t ⟨_, hr'⟩ (e w) := by
      apply Subtype.ext
      rw [he, coe_resCV_apply, coe_resV_apply, coe_resV_apply, coe_resCV_apply, ← hk,
        coe_mul_apply, coe_mul_apply, inv_apply_apply_O]
    rw [h1, hQr, hQr]
  obtain ⟨w₀, hw₀⟩ := exists_bilin_eq_of_additive hβnd (fun w => D.Q (e w) + D.Q w) hadd
  have hfix : ∀ r : Rbar S g t, resV haQ t r w₀ = w₀ := by
    intro r
    rw [← sub_eq_zero]
    refine hβnd.1 _ fun u => ?_
    obtain ⟨u', rfl⟩ : ∃ u', resV haQ t r u' = u :=
      ⟨(resV haQ t r).symm u, LinearEquiv.apply_symm_apply _ _⟩
    rw [LinearMap.map_sub₂, beta_apply_resV H C ht ht1 hVQ r, hw₀, hw₀, hδr, sub_self]
  have hwL : w₀ ∈ fixSpaceOf (LmodN S g t) := by
    rw [mem_fixSpaceOf]
    rintro a ⟨l, hl, hal⟩
    apply Subtype.ext
    rw [hal]
    exact congrArg Subtype.val (hfix ⟨l, Lbar_le_Rbar ht hl⟩)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (fixSpaceOf_LmodN_le H ht hwL)
  have hw0 : w₀ = 0 := by
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [← hc, zero_smul]
    · exfalso
      rw [one_smul] at hc
      have h1 := hfix ⟨S.ρ D.h, D.hh⟩
      rw [← hc, resV_aV haQ ht D.hh (mem_Lbar_of_pair H ht D.hh)] at h1
      have h2 := D.polar_aV_bV
      rw [h1, hpolβ, beta_isAlt H C ht ht1 hVQ (aV ht)] at h2
      exact zero_ne_one h2
  have h0 := hw₀ v
  rw [hw0, LinearMap.map_zero₂] at h0
  exact zmod2_eq_of_add_eq_zero h0.symm

theorem finrank_WV_le_two_mul_finrank_commWV_of_pair (D : Std H C ht ht1 hVQ)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hτc : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹))
    (hβ : beta H C ht ht1 hVQ (bV (mem_Lbar_mul_of_mem_Rbar H ht hk))
      (bV (mem_Lbar_mul_of_mem_Rbar H ht hk')) = 1) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≤
      2 * finrank (ZMod 2) (commWV S g t τ) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  set c : Vt S g t := bV htk with hc
  set c' : Vt S g t := bV htk' with hc'
  obtain ⟨k₀, hk₀⟩ := MonoidHom.mem_range.mp hτM
  have hakQ : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k.2 haQ
  have hcc' : (c' : S.Qt) = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) c := by
    rw [hc', coe_bV, hc, coe_bV, hτc]
  have hβcc' : beta H C ht ht1 hVQ c c' = 1 := hβ
  have hb' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g) := by
    intro hmem
    have hk'Q : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k'.2 haQ
    have h1 : (c' : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
      rw [hc', coe_bV]
      exact S.cl_mem_clSub ⟨hk'Q, hmem⟩ hk'Q
    have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk c').mpr h1
    rw [hβcc'] at h2
    exact one_ne_zero h2
  set h₁ : S.M := k' * k⁻¹ with hh₁
  have hh₁g : ((h₁ : S.M) : G) * ((k : G) * g) = (k' : G) * g := by
    rw [hh₁, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  have hh₁R : S.ρ h₁ ∈ Rbar S ((k : G) * g) t := by
    rw [Rbar_mul, hh₁, map_mul, map_inv]
    exact mul_mem hk' (inv_mem hk)
  have hb₁ : ((h₁ : S.M) : G) * ((k : G) * g) * S.z * (((h₁ : S.M) : G) * ((k : G) * g))⁻¹ ∉
      S.Qa ((k : G) * g) := by
    rw [hh₁g]; exact hb'
  have hVQ₁ := not_V_le_Qa_mul H hVQ hk
  have hP₁ := clSub_inf_clSub_le_Vt (H.mul k) (C.mul k) htk ht1 hVQ₁ hh₁R hb₁
    (RadBound.mul H D.hR hk)
  have hsup₁ := sup_eq_Wt (H.mul k) (C.mul k) htk ht1 hVQ₁ hh₁R hb₁ hP₁
  rw [hh₁g, Vt_mul] at hP₁
  rw [hh₁g, Wt_mul] at hsup₁
  set X := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t with hX
  set X' := S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t with hX'
  have hQa1 : S.QG ⊓ S.Qa ((k₀ : G) * ((k : G) * g)) = S.QG ⊓ S.Qa ((k' : G) * g) := by
    refine QG_inf_Qa_eq_of_cl_eq (conj_mem_QG' S k'.2 haQ) (conj_ne_z' S k'.2 H.conj_ne)
      (conj_mem_QG' S k₀.2 hakQ) ?_
    rw [← ρ_cl_conj_z S k₀ hakQ, ← coe_bV htk, hk₀, ← hc, ← hcc', hc', coe_bV]
  have hakQ' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∈ S.QG := conj_mem_QG' S k'.2 haQ
  have hQa2 : S.QG ⊓ S.Qa ((k₀ : G) * ((k' : G) * g)) = S.QG ⊓ S.Qa ((k : G) * g) := by
    refine QG_inf_Qa_eq_of_cl_eq hakQ (conj_ne_z' S k.2 H.conj_ne)
      (conj_mem_QG' S k₀.2 hakQ') ?_
    rw [← ρ_cl_conj_z S k₀ hakQ', ← coe_bV htk', hk₀, ← hc', hcc', ← coe_mul_apply, hττ]
    rw [hc, coe_bV]
    rfl
  have hτX : ∀ v ∈ X, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X' := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨?_, apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hv2⟩
    have := apply_mem_clSub_Qa_mul (g := (k : G) * g) k₀ hv1
    rwa [hQa1, hk₀] at this
  have hτX' : ∀ v ∈ X', (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨?_, apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hv2⟩
    have := apply_mem_clSub_Qa_mul (g := (k' : G) * g) k₀ hv1
    rwa [hQa2, hk₀] at this
  have hVW := Vt_le_Wt H ht1
  have hmemX : ∀ y : Vt S g t, beta H C ht ht1 hVQ c y = 0 → (y : S.Qt) ∈ X ⊓ Vt S g t :=
    fun y hy => ⟨⟨(beta_bV_eq_zero_iff H C ht ht1 hVQ hk htk y).mp hy, hVW y.2⟩, y.2⟩
  have hmemX' : ∀ y : Vt S g t, beta H C ht ht1 hVQ c' y = 0 → (y : S.Qt) ∈ X' ⊓ Vt S g t :=
    fun y hy => ⟨⟨(beta_bV_eq_zero_iff H C ht ht1 hVQ hk' htk' y).mp hy, hVW y.2⟩, y.2⟩
  have hsplit : X ⊓ Vt S g t ⊔ X' ⊓ Vt S g t = Vt S g t := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun v hv => ?_
    set y : Vt S g t := ⟨v, hv⟩ with hy
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ c y) with h0 | h1
    · exact Submodule.mem_sup_left (hmemX y h0)
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ c' y) with h0' | h1'
    · exact Submodule.mem_sup_right (hmemX' y h0')
    have hc0 : c ≠ 0 := by
      rintro h
      rw [h, map_zero, LinearMap.zero_apply] at hβcc'
      exact zero_ne_one hβcc'
    have hcc'ne : c ≠ c' := by
      intro h
      rw [← h, (beta_isAlt H C ht ht1 hVQ) c] at hβcc'
      exact zero_ne_one hβcc'
    obtain ⟨w, hw1, hw2⟩ := exists_apply_eq_one_eq_zero (beta_nondegenerate H C ht ht1 hVQ) hc0
      hcc'ne
    have hyw : beta H C ht ht1 hVQ c (y - w) = 0 := by
      rw [map_sub, h1, hw1, sub_self]
    have e : v = ((y - w : Vt S g t) : S.Qt) + (w : S.Qt) := by
      rw [Submodule.coe_sub, sub_add_cancel]
    rw [e]
    exact Submodule.add_mem_sup (hmemX _ hyw) (hmemX' w hw2)
  exact finrank_map_mkQ_le_two_mul (τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap hVW inf_le_right
    inf_le_right hsup₁ (fun v hv => hP₁ ⟨hv.1.1, hv.2.1⟩) hsplit hτX hτX'

theorem step1_fix_Vt_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    ∀ τ ∈ conjCentM S t, ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  rintro τ ⟨hτM, hτt, x, hxM, hxτ⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hτv⟩ := hcon
  have haQ := H.conj_mem
  have hτC : τ ∈ CMt S t := mem_CMt.mpr ⟨hτM, hτt⟩
  set y : CMt S t := ⟨τ, hτC⟩ with hy
  set e := resCV S g haQ t y with he
  have hpolβ : ∀ u w : Vt S g t, polar D.Q u w = beta H C ht ht1 hVQ u w := fun u w => by
    rw [← polarBilin_apply_apply, D.hpol]
  have hmove : ∃ α ∈ orbitOf (RmodN S g t) (aV ht), e α ≠ α := by
    by_contra h
    push Not at h
    apply hτv
    have hle : Submodule.span (ZMod 2) (orbitOf (RmodN S g t) (aV ht)) ≤ fixSpace e := by
      rw [Submodule.span_le]
      intro α hα
      exact mem_fixSpace.mpr (h α hα)
    rw [span_orbitOf_RmodN H ht] at hle
    exact congrArg Subtype.val (mem_fixSpace.mp
      (hle (Submodule.mem_top : (⟨v, hv⟩ : Vt S g t) ∈ ⊤)))
  obtain ⟨α, hα, hτα⟩ := hmove
  set α' := e α with hα'
  have horb0 : ∀ β ∈ orbitOf (RmodN S g t) (aV ht), β ≠ 0 := by
    rintro _ ⟨z, -, rfl⟩ h
    exact aV_ne_zero H ht (z.injective (h.trans (map_zero z).symm))
  have hα0 := horb0 α hα
  have hα'0 : α' ≠ 0 := fun h => hα0 (e.injective (h.trans (map_zero e).symm))
  have hQα : D.Q α = 0 := (D.hsing α hα0).mpr hα
  have hQα' : D.Q α' = 0 := by rw [hα', he, D.Q_resCV]; exact hQα
  have hα'orb : α' ∈ orbitOf (RmodN S g t) (aV ht) := (D.hsing α' hα'0).mp hQα'
  have hβ1 : beta H C ht ht1 hVQ α α' = 1 := by
    rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ α α') with h0 | h1
    · exfalso
      have hli : LinearIndependent (ZMod 2) ![α, α'] := by
        refine (LinearIndependent.pair_iff' hα0).mpr fun a ha => ?_
        rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
        · rw [zero_smul] at ha; exact hα'0 ha.symm
        · rw [one_smul] at ha; exact hτα ha.symm
      have hT : ∀ w ∈ Submodule.span (ZMod 2) {α, α'}, D.Q w = 0 := by
        intro w hw
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
        rw [QuadraticMap.map_add D.Q (a • α) (b • α'), QuadraticMap.map_smul,
          QuadraticMap.map_smul, hQα, hQα', polar_smul_left, polar_smul_right, hpolβ, h0]
        simp
      have h2 := hmin _ hT
      rw [finrank_span_pair hli, hm2] at h2
      omega
    · exact h1
  obtain ⟨k, hk, hkα⟩ := exists_of_mem_orbit ((mem_orbitOf_RmodN_iff haQ ht).mp hα) haQ
  obtain ⟨k', hk', hk'α⟩ := exists_of_mem_orbit ((mem_orbitOf_RmodN_iff haQ ht).mp hα'orb) haQ
  have hcα : bV (mem_Lbar_mul_of_mem_Rbar H ht hk) = α := Subtype.ext (by rw [coe_bV, hkα])
  have hcα' : bV (mem_Lbar_mul_of_mem_Rbar H ht hk') = α' :=
    Subtype.ext (by rw [coe_bV, hk'α])
  have hτc : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) := by
    rw [← hkα, ← hk'α, hα', he, coe_resCV_apply]
  have hlow := finrank_WV_le_two_mul_finrank_commWV_of_pair D hxM hxτ hτt hk hk' hτc
    (by rw [hcα, hcα']; exact hβ1)
  have hWV := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
  have hfilt := finrank_commSpace_ge (S := S) (g := g) (t := t) (τ := τ)
    (fun w hw => apply_mem_Vt_of_mem_CMt haQ hτC hw)
    (fun w hw => apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hw) (Vt_le_Wt H ht1)
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hVpos : 0 < finrank (ZMod 2)
      ((Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    apply hτv
    have hmem : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
        (Vt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  rw [D.hdim, hm2] at hdimτ
  omega

end CFSG.LargeExtraspecial.S8
