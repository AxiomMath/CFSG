module

public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.Monster.B.CTIB.HOuter
meta import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFactsInputs
public import Certificates.Certificate3128
public import Certificates.Certificate3121
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3044
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB
  CFSG.Monster.B.CTIB.Native CFSG.Monster.B.GSide CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4Radical
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped commutatorElement

theorem mul_self_ne_cE'
    (y : Eam) : y * y ≠ cE' := by
  intro h
  refine native_inner_square_fusion.2.1 (vStabEam.symm y) ?_
  rw [← map_mul, h, ← vStabEam_cV0, MulEquiv.symm_apply_apply]

theorem sq_eq_one_of_sq_mem_center
    (a : commutator Eam)
    (ha : a ^ 2 ∈ Subgroup.center (commutator Eam)) : a ^ 2 = 1 := by
  have hc2 : orderOf cE' = 2 := by rw [← Nat.card_zpowers, natCard_zpowers_cE'_eq_two]
  have hmem : ((a ^ 2 : commutator Eam) : Eam) ∈ Subgroup.zpowers cE' := by
    rw [← short_F4_derived_standard_perfect_cover.2.2.2.1]
    exact ⟨_, ha, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hc2 hmem with h | h
  · exact Subtype.ext h
  · refine absurd ?_ (mul_self_ne_cE' a)
    rw [← h, Subgroup.coe_pow, sq]

theorem sq_eq_one_of_sq_mem_center_of_mulEquiv
    {L : Type*} [Group L]
    (φ : L ≃* commutator Eam) (a : L) (ha : a ^ 2 ∈ Subgroup.center L) : a ^ 2 = 1 := by
  apply φ.injective
  rw [map_one, map_pow]
  refine sq_eq_one_of_sq_mem_center (φ a) ?_
  rw [← map_pow]
  exact (mem_center_iff_of_mulEquiv φ).1 ha

theorem fgOK_eq_true : fgOK = true :=
  Certificates.certificate3128

theorem qS_mul_hs6
    (n : ℕ) :
    qS n * hs 6 = hs 6 * qS (autApply gArr (liftImgsN 6).toArray n) := by
  rw [liftImgsN_eq, ← conj_hs_qS (Or.inl rfl) n]
  group

theorem pair_facts
    {v a : ℕ} (h : fgPairOK v a = true) :
    Commute (qS a) e2158 ∧ rs 6 * qS a = qS a * (rs 6 * qS v) ∧ Commute (qS v) (rs 6) ∧
      Commute (qS v) e2158 ∧ qS v * qS v = 1 := by
  simp only [fgPairOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [e2158_eq, rs6_eq, cosetElt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change qS a * qS 4456968 = qS 4456968 * qS a
    rw [qS_mul, qS_mul, h1]
  · calc hs 6 * qS 10541 * qS a = hs 6 * qS (qmul gArr 10541 a) := by rw [mul_assoc, qS_mul]
      _ = hs 6 * (qS (autApply gArr (liftImgsN 6).toArray a) * qS 10541 * qS v) := by
          rw [h2, ← qS_mul, ← qS_mul]
      _ = qS a * hs 6 * qS 10541 * qS v := by rw [qS_mul_hs6]; group
      _ = qS a * (hs 6 * qS 10541 * qS v) := by group
  · change qS v * (hs 6 * qS 10541) = hs 6 * qS 10541 * qS v
    calc qS v * (hs 6 * qS 10541) =
          hs 6 * (qS (autApply gArr (liftImgsN 6).toArray v) * qS 10541) := by
          rw [← mul_assoc, qS_mul_hs6, mul_assoc]
      _ = hs 6 * qS 10541 * qS v := by rw [qS_mul, ← h3, ← qS_mul, mul_assoc]
  · change qS v * qS 4456968 = qS 4456968 * qS v
    rw [qS_mul, qS_mul, h4]
  · rw [qS_mul, h5, qS_zero]

noncomputable abbrev CSe :
    Subgroup Sbp := Subgroup.centralizer ({e2158} : Set Sbp)

@[expose] noncomputable def qC
    {n : ℕ} (h : Commute (qS n) e2158) : CSe :=
  ⟨qS n, Subgroup.mem_centralizer_singleton_iff.2 h⟩

theorem coe_qC
    {n : ℕ} (h : Commute (qS n) e2158) : ((qC h : CSe) : Sbp) = qS n := rfl

theorem good_rs6
    {v a : ℕ} (h : fgPairOK v a = true) :
    rs 6 * qS a = qS a * (rs 6 * qS v) ∧ Commute (qS v) (rs 6) :=
  ⟨(pair_facts h).2.1, (pair_facts h).2.2.1⟩

theorem good_mul {v a : ℕ} {z t : Sbp} (hza : Commute z (qS a)) (hzv : Commute z (qS v))
    (ht : t * qS a = qS a * (t * qS v) ∧ Commute (qS v) t) :
    z * t * qS a = qS a * (z * t * qS v) ∧ Commute (qS v) (z * t) := by
  refine ⟨?_, hzv.symm.mul_right ht.2⟩
  rw [mul_assoc, ht.1, ← mul_assoc, hza.eq]
  group

theorem pair_Ce
    {v a : ℕ} (h : fgPairOK v a = true) {t : CSe}
    (ht : (t : Sbp) * qS a = qS a * ((t : Sbp) * qS v) ∧ Commute (qS v) (t : Sbp)) :
    qC (pair_facts h).2.2.2.1 ∈ commutator CSe ∧ Commute (qC (pair_facts h).2.2.2.1) t ∧
      IsConj (qC (pair_facts h).2.2.2.1 * t) t := by
  obtain ⟨ha, -, -, hve, -⟩ := pair_facts h
  have hta : t * qC ha = qC ha * (t * qC hve) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, coe_qC, coe_qC]
    exact ht.1
  have hvt : Commute (qC hve) t := by
    show qC hve * t = t * qC hve
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_qC]
    exact ht.2.eq
  have hta' : (qC ha)⁻¹ * t * qC ha = t * qC hve := by rw [mul_assoc, hta, inv_mul_cancel_left]
  refine ⟨?_, hvt, ?_⟩
  · show qC hve ∈ commutator CSe
    have hc : ⁅t⁻¹, (qC ha)⁻¹⁆ = qC hve := by
      calc ⁅t⁻¹, (qC ha)⁻¹⁆ = t⁻¹ * ((qC ha)⁻¹ * t * qC ha) := by
            rw [commutatorElement_def]; group
        _ = qC hve := by rw [hta', inv_mul_cancel_left]
    rw [← hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · refine (isConj_iff.2 ⟨(qC ha)⁻¹, ?_⟩).symm
    rw [inv_inv, hta', hvt.eq]

theorem four_Ce
    {t : CSe}
    (ht : ∀ {v a : ℕ}, fgPairOK v a = true →
      (t : Sbp) * qS a = qS a * ((t : Sbp) * qS v) ∧ Commute (qS v) (t : Sbp)) :
    ∃ V : Subgroup CSe, V ≤ commutator CSe ∧ Nat.card V = 4 ∧
      V ≤ Subgroup.centralizer ({t} : Set CSe) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * t) t := by
  have h := fgOK_eq_true
  simp only [fgOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₁₂⟩, h₂₁⟩ := h
  have p₁ := pair_Ce h₁ (ht h₁)
  have p₂ := pair_Ce h₂ (ht h₂)
  have p₃ := pair_Ce h₃ (ht h₃)
  have e₁₂ : qC (pair_facts h₁).2.2.2.1 * qC (pair_facts h₂).2.2.2.1 =
      qC (pair_facts h₃).2.2.2.1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_qC, coe_qC, coe_qC, qS_mul, h₁₂]
  have e₂₁ : qC (pair_facts h₂).2.2.2.1 * qC (pair_facts h₁).2.2.2.1 =
      qC (pair_facts h₃).2.2.2.1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_qC, coe_qC, coe_qC, qS_mul, h₂₁]
  have hsq : ∀ {v a : ℕ} (h : fgPairOK v a = true),
      qC (pair_facts h).2.2.2.1 * qC (pair_facts h).2.2.2.1 = 1 := by
    intro v a h
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_qC, Subgroup.coe_one]
    exact (pair_facts h).2.2.2.2
  have hne : ∀ {v a : ℕ} (h : fgPairOK v a = true), v ≠ 0 → v < 2 ^ 23 →
      qC (pair_facts h).2.2.2.1 ≠ 1 := by
    intro v a h hv0 hv h1
    have h2 := congrArg Subtype.val h1
    rw [coe_qC, Subgroup.coe_one] at h2
    exact hv0 ((qS_eq_one_iff hv).1 h2)
  have hlt : ∀ n, n < 2 ^ 23 → n ∈ Set.Iio (2 ^ 23) := fun _ h => h
  refine exists_four_of_pair (hsq h₁) (hsq h₂) (e₁₂.trans e₂₁.symm)
    (hne h₁ (by norm_num) (by norm_num)) (hne h₂ (by norm_num) (by norm_num)) ?_ ?_
  · intro h1
    have h2 := congrArg Subtype.val h1
    rw [coe_qC, coe_qC] at h2
    have h3 := qS_injOn (hlt 5131954 (by norm_num)) (hlt 6537621 (by norm_num)) h2
    norm_num at h3
  · rintro w (rfl | rfl | rfl)
    · exact p₁
    · exact p₂
    · rw [e₁₂]
      exact p₃

theorem frame_mem
    {g : Shat}
    (hg : g⁻¹ * clabelS cv0 * g = sEquiv e2158) (s : CSe) :
    g * sEquiv (s : Sbp) * g⁻¹ ∈ vStab cv0 := by
  rw [← CTIB.commute_clabelS_iff (global_label_of_ambient ambientRootOrbitsHyp).1,
    show clabelS cv0 = g * sEquiv e2158 * g⁻¹ by rw [← hg]; group]
  have hc : Commute (s : Sbp) e2158 := Subgroup.mem_centralizer_singleton_iff.1 s.2
  simpa only [MulAut.conj_apply] using (hc.map sEquiv).map (MulAut.conj g)

@[expose] noncomputable def frameHom
    {g : Shat}
    (hg : g⁻¹ * clabelS cv0 * g = sEquiv e2158) :
    CSe →* Eam :=
  vStabEam.toMonoidHom.comp
    (((MulAut.conj g).toMonoidHom.comp (sEquiv.toMonoidHom.comp CSe.subtype)).codRestrict
      (vStab cv0) fun s => by simpa using frame_mem hg s)

theorem coe_frameHom
    {g : Shat} (hg : g⁻¹ * clabelS cv0 * g = sEquiv e2158) (s : CSe) :
    ((frameHom hg s : Eam) : Dfull) = ((g * sEquiv (s : Sbp) * g⁻¹ : Shat) : Dfull) :=
  rfl

theorem frameHom_injective
    {g : Shat}
    (hg : g⁻¹ * clabelS cv0 * g = sEquiv e2158) :
    Function.Injective (frameHom hg) := by
  intro s s' h
  have h1 : g * sEquiv (s : Sbp) * g⁻¹ = g * sEquiv (s' : Sbp) * g⁻¹ :=
    Subtype.ext ((coe_frameHom hg s).symm.trans
      ((congrArg Subtype.val h).trans (coe_frameHom hg s')))
  exact Subtype.ext (sEquiv.injective (mul_left_cancel (mul_right_cancel h1)))

theorem frameHom_eq
    {g : Shat}
    (hg : g⁻¹ * clabelS cv0 * g = sEquiv e2158) {s : CSe}
    {w : vStab cv0} (hw : g⁻¹ * (w : Shat) * g = sEquiv (s : Sbp)) :
    frameHom hg s = vStabEam w := by
  apply Subtype.ext
  rw [coe_frameHom, coe_vStabEam, ← hw, show g * (g⁻¹ * (w : Shat) * g) * g⁻¹ = w by group]

theorem cE'_mem_commutator :
    cE' ∈ commutator Eam := by
  have h := Subgroup.mem_zpowers cE'
  rw [← short_F4_derived_standard_perfect_cover.2.2.2.1] at h
  obtain ⟨w, -, hw⟩ := h
  rw [← hw]
  exact w.2

theorem eq_one_or_eq_cE'_of_map_eq_one
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ StdF4.rootClass} (hρ : IsCompatLocal cv0 ρ iv) {w : Eam}
    (hw : ρ (vStabEam.symm w) = 1) : w = 1 ∨ w = cE' := by
  have hmem : vStabEam.symm w ∈ Subgroup.zpowers (cStab cv0) :=
    ker_eq_zpowers_cStab hρ.2.1 ▸ MonoidHom.mem_ker.2 hw
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_cStab cv0) hmem with h | h
  · left
    rw [← vStabEam.apply_symm_apply w, h, map_one vStabEam]
  · right
    rw [← vStabEam.apply_symm_apply w, h, show cStab cv0 = cV0 from rfl, vStabEam_cV0]

theorem map_not_mem_Ginl
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ StdF4.rootClass} (hρ : IsCompatLocal cv0 ρ iv) {y : Eam}
    (hy : y ∉ commutator Eam) : ρ (vStabEam.symm y) ∉ Ginl := by
  have hsurj : Function.Surjective (ρ.comp vStabEam.symm.toMonoidHom) :=
    hρ.1.comp vStabEam.symm.surjective
  have hmap : (commutator Eam).map (ρ.comp vStabEam.symm.toMonoidHom) = Ginl := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 hsurj, ← _root_.commutator_def,
      commutator_GStar]
  intro hmem
  rw [← hmap] at hmem
  obtain ⟨w, hw, hwy⟩ := hmem
  have hwy' : ρ (vStabEam.symm w) = ρ (vStabEam.symm y) := hwy
  have hy' : y = w * (w⁻¹ * y) := (mul_inv_cancel_left w y).symm
  have hk : ρ (vStabEam.symm (w⁻¹ * y)) = 1 := by
    simp only [map_mul, map_inv, hwy', inv_mul_cancel]
  rcases eq_one_or_eq_cE'_of_map_eq_one hρ hk with h | h
  · exact hy (by rw [hy', h, mul_one]; exact hw)
  · exact hy (by rw [hy', h]; exact mul_mem hw cE'_mem_commutator)

theorem isConj_map_of_outer_involution
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ StdF4.rootClass} (hρ : IsCompatLocal cv0 ρ iv) {y : Eam}
    (hy : y ∉ commutator Eam) (hy2 : y * y = 1) :
    IsConj (ρ (vStabEam.symm y)) betaStarElt ∨
      IsConj (ρ (vStabEam.symm y)) (StdF4.rootStar * betaStarElt) := by
  have hright : (ρ (vStabEam.symm y)).right ≠ 1 := by
    intro h
    apply map_not_mem_Ginl hρ hy
    change _ ∈ (SemidirectProduct.inl : stdGroup →* GStar).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
      SemidirectProduct.rightHom_eq_right]
    exact h
  have hform := eq_inl_mul_beta hright
  have hsq' : ρ (vStabEam.symm y) * ρ (vStabEam.symm y) = 1 := by
    rw [← map_mul ρ, ← map_mul vStabEam.symm, hy2, map_one vStabEam.symm, map_one ρ]
  have hsq : (SemidirectProduct.inl (ρ (vStabEam.symm y)).left * betaStarElt : GStar) ^ 2 = 1 := by
    rw [← hform, sq]
    exact hsq'
  rcases FieldInvF4.xor_conj_of_sq_eq_one hsq with ⟨⟨k, hk⟩, -⟩ | ⟨⟨k, hk⟩, -⟩
  · refine Or.inl (isConj_iff.2 ⟨SemidirectProduct.inl k, ?_⟩)
    rw [hform]
    exact hk
  · refine Or.inr (isConj_iff.2 ⟨SemidirectProduct.inl k, ?_⟩)
    rw [hform]
    exact hk

theorem isConj_vStabEam
    {y : Eam} {w : vStab cv0} (h : IsConj (vStabEam.symm y) w) :
    IsConj y (vStabEam w) :=
  (vStabEam.apply_symm_apply y) ▸ vStabEam.toMonoidHom.map_isConj h

theorem isConj_of_outer_involution
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ StdF4.rootClass} (hρ : IsCompatLocal cv0 ρ iv)
    {b x : vStab cv0}
    (hcl1 : ∀ y : vStab cv0, IsConj (ρ y) betaStarElt ↔ IsConj y b ∨ IsConj y (cStab cv0 * b))
    (hcl2 : ∀ y : vStab cv0, IsConj (ρ y) (StdF4.rootStar * betaStarElt) ↔
      IsConj y (b * x) ∨ IsConj y (cStab cv0 * (b * x)))
    {y : Eam} (hy : y ∉ commutator Eam) (hy2 : y * y = 1) :
    (IsConj y (vStabEam b) ∨ IsConj y (vStabEam (cStab cv0 * b))) ∨
      (IsConj y (vStabEam (b * x)) ∨ IsConj y (vStabEam (cStab cv0 * (b * x)))) :=
  (isConj_map_of_outer_involution hρ hy hy2).imp
    (fun hc => ((hcl1 _).1 hc).imp isConj_vStabEam isConj_vStabEam)
    (fun hc => ((hcl2 _).1 hc).imp isConj_vStabEam isConj_vStabEam)

@[expose] noncomputable def rC :
    CSe :=
  ⟨rs 6, Subgroup.mem_centralizer_singleton_iff.2 commute_rs6_e2158⟩

@[expose] noncomputable def eC :
    CSe := ⟨e2158, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] noncomputable def xC :
    CSe :=
  ⟨xs, Subgroup.mem_centralizer_singleton_iff.2 commute_e2158_xs.symm⟩

theorem coe_rC :
    (rC : Sbp) = rs 6 := rfl

theorem coe_eC :
    (eC : Sbp) = e2158 := rfl

theorem coe_xC :
    (xC : Sbp) = xs := rfl

theorem exists_fours_group_of_outer_involution
    {y : Eam}
    (hy : y ∉ commutator Eam)
    (hy2 : y * y = 1) :
    ∃ V : Subgroup Eam, V ≤ commutator Eam ∧ Nat.card V = 4 ∧
      V ≤ Subgroup.centralizer ({y} : Set Eam) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨-, -, b, x, -, -, -, -, -, -, -, ⟨g, hg1, hg2, hg3⟩, -, -, -, -, hcl1, hcl2, -⟩ :=
    native_H_outer_involution_classes hρ
  have hmapC : (commutator CSe).map (frameHom hg1) ≤ commutator Eam :=
    (map_commutator_eq _ _).le.trans (Subgroup.commutator_mono le_top le_top)
  have key : ∀ (t : CSe) (w : vStab cv0), (∀ {v a : ℕ}, fgPairOK v a = true →
      (t : Sbp) * qS a = qS a * ((t : Sbp) * qS v) ∧ Commute (qS v) (t : Sbp)) →
      frameHom hg1 t = vStabEam w → IsConj y (vStabEam w) →
      ∃ V : Subgroup Eam, V ≤ commutator Eam ∧ Nat.card V = 4 ∧
        V ≤ Subgroup.centralizer ({y} : Set Eam) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
    intro t w ht hw hc
    have h := exists_four_map (frameHom hg1) (frameHom_injective hg1) hmapC (four_Ce ht)
    rw [hw] at h
    exact exists_four_of_isConj hc.symm h
  have hb : frameHom hg1 rC = vStabEam b := frameHom_eq hg1 hg2
  have he : frameHom hg1 eC = vStabEam (cStab cv0) := frameHom_eq hg1 hg1
  have hx : frameHom hg1 xC = vStabEam x := frameHom_eq hg1 hg3
  have hxz : ∀ n, Commute xs (qS n) := fun n => xs_comm (qS_mem n)
  rcases isConj_of_outer_involution hρ hcl1 hcl2 hy hy2 with (h | h) | (h | h)
  · refine key rC b (fun hp => ?_) hb h
    rw [coe_rC]
    exact good_rs6 hp
  · refine key (eC * rC) (cStab cv0 * b) (fun hp => ?_) (by simp only [map_mul, he, hb]) h
    rw [Subgroup.coe_mul, coe_eC, coe_rC]
    exact good_mul (pair_facts hp).1.symm (pair_facts hp).2.2.2.1.symm (good_rs6 hp)
  · refine key (rC * xC) (b * x) (fun hp => ?_) (by simp only [map_mul, hb, hx]) h
    rw [Subgroup.coe_mul, coe_rC, coe_xC, commute_rs6_xs.eq]
    exact good_mul (hxz _) (hxz _) (good_rs6 hp)
  · refine key (eC * (rC * xC)) (cStab cv0 * (b * x)) (fun hp => ?_)
      (by simp only [map_mul, he, hb, hx]) h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eC, coe_rC, coe_xC, commute_rs6_xs.eq,
      ← mul_assoc]
    exact good_mul ((pair_facts hp).1.symm.mul_left (hxz _))
      ((pair_facts hp).2.2.2.1.symm.mul_left (hxz _)) (good_rs6 hp)

end CFSG.EvenSmallLie.TwoE6
