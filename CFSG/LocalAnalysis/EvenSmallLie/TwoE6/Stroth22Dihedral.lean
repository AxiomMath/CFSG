module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
public import CFSG.Monster.B.GSide.HInnerFusionY3
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22DihedralInputs
public import Certificates.Certificate3140
public import Certificates.Certificate3100
public import Certificates.Certificate3110
public import Certificates.Certificate3122
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
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3128
public import Certificates.Certificate3135
public import Certificates.Certificate3136
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
public import Certificates.Certificate1003
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3032
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.GSide CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def D8At
    (c y : Sbp) : Prop :=
  ∃ i₁ i₂ : Sbp, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧ i₁ * c = c * i₁ ∧ i₂ * c = c * i₂ ∧
    ((βr i₁) - 1).rank ≠ 2158 ∧ ((βr (c * i₁)) - 1).rank ≠ 2158 ∧
    ((βr i₂) - 1).rank ≠ 2158 ∧ ((βr (c * i₂)) - 1).rank ≠ 2158 ∧
    i₁ * i₂ * (i₁ * i₂) = y

section Generic

variable {M : Type*} [Group M]

theorem conj_inv_data {g c c₀ i : M} (hc : g * c * g⁻¹ = c₀) (h1 : i * i = 1)
    (hci : i * c₀ = c₀ * i) :
    g⁻¹ * i * g * (g⁻¹ * i * g) = 1 ∧ g⁻¹ * i * g * c = c * (g⁻¹ * i * g) ∧
      c * (g⁻¹ * i * g) = g⁻¹ * (c₀ * i) * g := by
  have ec : c = g⁻¹ * c₀ * g := by rw [← hc]; group
  subst ec
  refine ⟨?_, ?_, by group⟩
  · calc g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g := by group
      _ = 1 := by rw [h1]; group
  · calc g⁻¹ * i * g * (g⁻¹ * c₀ * g) = g⁻¹ * (i * c₀) * g := by group
      _ = g⁻¹ * (c₀ * i) * g := by rw [hci]
      _ = g⁻¹ * c₀ * g * (g⁻¹ * i * g) := by group

theorem conj_inv_sq {g y y₀ i₁ i₂ : M} (hy : g * y * g⁻¹ = y₀)
    (h : i₁ * i₂ * (i₁ * i₂) = y₀) :
    g⁻¹ * i₁ * g * (g⁻¹ * i₂ * g) * (g⁻¹ * i₁ * g * (g⁻¹ * i₂ * g)) = y := by
  have ey : y = g⁻¹ * y₀ * g := by rw [← hy]; group
  rw [ey, ← h]
  group

end Generic

theorem rank_conj'
    (g y : Sbp) : ((βr (g * y * g⁻¹)) - 1).rank =
    ((βr y) - 1).rank := by
  have h := rank_conj g⁻¹ y
  rwa [inv_inv] at h

theorem D8At.of_conj
    {c y c₀ y₀ g : Sbp} (h : D8At c₀ y₀) (hc : g * c * g⁻¹ = c₀)
    (hy : g * y * g⁻¹ = y₀) : D8At c y := by
  obtain ⟨i₁, i₂, h1, h2, hc1, hc2, r1, r1', r2, r2', hy₀⟩ := h
  obtain ⟨a1, b1, e1⟩ := conj_inv_data hc h1 hc1
  obtain ⟨a2, b2, e2⟩ := conj_inv_data hc h2 hc2
  refine ⟨g⁻¹ * i₁ * g, g⁻¹ * i₂ * g, a1, a2, b1, b2, ?_, ?_, ?_, ?_, conj_inv_sq hy hy₀⟩
  · rw [rank_conj]; exact r1
  · rw [e1, rank_conj]; exact r1'
  · rw [rank_conj]; exact r2
  · rw [e2, rank_conj]; exact r2'

theorem sEquiv_mem_vStab
    {s : Sbp} (hs : s * labelS = labelS * s) : sEquiv s ∈ vStab
    cv0 :=
  (commute_labelS_iff_mem s).1 hs

theorem vStab_mul_self
    {i : Sbp}
    (hci : i * labelS = labelS * i) (hi2 : i * i = 1) :
    (⟨sEquiv i, sEquiv_mem_vStab hci⟩ : vStab cv0) * ⟨sEquiv i, sEquiv_mem_vStab hci⟩ = 1 :=
  Subtype.ext ((map_mul sEquiv i i).symm.trans ((congrArg sEquiv hi2).trans (map_one sEquiv)))

theorem rkH_vStab
    {i : Sbp} (hci : i * labelS = labelS * i) :
    rkH ⟨sEquiv i, sEquiv_mem_vStab hci⟩ = ((βr i) - 1).rank := by
  rw [rkH, MulEquiv.symm_apply_apply]

theorem rkH_cV0_mul_vStab
    {i : Sbp} (hci : i * labelS = labelS * i) :
    rkH (cV0 * ⟨sEquiv i, sEquiv_mem_vStab hci⟩) = ((βr (labelS * i)) - 1).rank := by
  have e : sEquiv.symm ((cV0 * ⟨sEquiv i, sEquiv_mem_vStab hci⟩ : vStab cv0) : Shat) =
      labelS * i :=
    (map_mul sEquiv.symm _ _).trans (by rw [sEquiv_symm_cV0, MulEquiv.symm_apply_apply])
  rw [rkH, e]

theorem vStab_mem_commutator
    {i : Sbp} (hci : i * labelS = labelS * i) (hi2 : i * i = 1)
    (ri : ((βr i) - 1).rank ≠ 2158) (ri' : ((βr (labelS * i)) - 1).rank ≠ 2158) :
    (⟨sEquiv i, sEquiv_mem_vStab hci⟩ : vStab cv0) ∈ commutator (vStab cv0) :=
  mem_commutator_of_rkH (vStab_mul_self hci hi2) (by rw [rkH_vStab hci]; exact ri)
    (by rw [rkH_cV0_mul_vStab hci]; exact ri')

theorem exists_dihedral_of_D8At
    {s : Sbp} (h : D8At labelS s) (hsc : s * labelS = labelS * s) :
    ∃ a₁ ∈ commutator (vStab cv0), ∃ a₂ ∈ commutator (vStab cv0), a₁ * a₁ = 1 ∧ a₂ * a₂ = 1 ∧
      a₁ * a₂ * (a₁ * a₂) = ⟨sEquiv s, sEquiv_mem_vStab hsc⟩ := by
  obtain ⟨i₁, i₂, h1, h2, hc1, hc2, r1, r1', r2, r2', hy⟩ := h
  refine ⟨_, vStab_mem_commutator hc1 h1 r1 r1', _, vStab_mem_commutator hc2 h2 r2 r2',
    vStab_mul_self hc1 h1, vStab_mul_self hc2 h2, Subtype.ext ?_⟩
  show sEquiv i₁ * sEquiv i₂ * (sEquiv i₁ * sEquiv i₂) = sEquiv s
  calc sEquiv i₁ * sEquiv i₂ * (sEquiv i₁ * sEquiv i₂) = sEquiv (i₁ * i₂ * (i₁ * i₂)) :=
        by simp only [map_mul]
    _ = sEquiv s := congrArg sEquiv hy

theorem d8WitnessOK_eq_true : d8WitnessOK = true :=
  Certificates.certificate3140

theorem d8Witness_parts :
    qmul gArr 2 2 = 0 ∧ qmul gArr 32 32 = 0 ∧ qmul gArr 2 1 = qmul gArr 1 2 ∧
    qmul gArr 32 1 = qmul gArr 1 32 ∧
    qmul gArr (qmul gArr 2 32) (qmul gArr 2 32) = 2 ^ 22 ∧
    qmul gArr (qmul gArr 1 2) (qmul gArr 1 2) = 0 ∧
    qmul gArr (qmul gArr 1 32) (qmul gArr 1 32) = 0 ∧
    qmul gArr 9 9 = 0 ∧ qmul gArr 3162 3162 = 0 ∧
    qmul gArr 3162 128 = qmul gArr 128 3162 ∧
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsN 8).toArray 3162) 3162) =
      5449715 ∧
    qmul gArr 2 1255411 = qmul gArr (qmul gArr 1255411 2) (2 ^ 22) ∧
    qmul gArr (qmul gArr 128 2) (qmul gArr 128 2) = 0 ∧
    qmul gArr (qmul gArr 128 9) (qmul gArr 128 9) = 0 ∧
    qmul gArr (qmul gArr 128 3162) (qmul gArr 128 3162) = 0 ∧
    qmul gArr 1255411 (2 ^ 22) = 5449715 := by
  have h := d8WitnessOK_eq_true
  simp only [d8WitnessOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem qS_mul_self_of_code
    {n : ℕ} (h : qmul gArr n n = 0) : qS n * qS n = 1 := by
  rw [qS_mul, h, qS_zero]

theorem rank_qS_ne_2158
    {n : ℕ} (hn : n < 2 ^ 23) (h2 : qS n * qS n = 1) :
    ((βr (qS n)) - 1).rank ≠ 2158 := by
  obtain ⟨-, h1, h3⟩ := innerRank_spec hn
  by_cases hk : innerTyRank (innerTy innerTab n) = 1
  · exact absurd ((h1 hk).symm.trans h2) xs_ne_one
  · rw [(h3 hk).2]
    unfold innerTyRank
    generalize innerTy innerTab n = k
    rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp

theorem rank_qS_ne_2158'
    {n : ℕ} (h2 : qmul gArr n n = 0) (hn : n < 2 ^ 23) :
    ((βr (qS n)) - 1).rank ≠ 2158 :=
  rank_qS_ne_2158 hn (qS_mul_self_of_code h2)

theorem hs8_mul_self :
    hs 8 * hs 8 = 1 := by
  rw [← sq]
  exact hs8_sq

theorem hs8_comm_qS128 :
    hs 8 * qS 128 = qS 128 * hs 8 := by
  have h := cosetElt8_comm (n := 0) (by rw [show qmul gArr 128 0 = 128 by rfl,
    show qmul gArr 0 128 = 128 by rfl])
  rwa [cosetElt, qS_zero, mul_one] at h

theorem rank_hs8 :
    ((βr (hs 8)) - 1).rank = 2168 := by
  have h := rank_rs (i := 9) (by norm_num)
  have e0 : rs 9 = hs 8 * qS 0 := rfl
  have e : rs 9 = hs 8 := by
    rw [e0, qS_zero, mul_one]
  rw [e] at h
  exact h

theorem rank_qS128_mul_hs8 :
    ((βr (qS 128 * hs 8)) - 1).rank = 2168 := by
  have h := rank_rs (i := 10) (by norm_num)
  have e : rs 10 = qS 128 * hs 8 := by
    rw [← hs8_comm_qS128]
    rfl
  rw [e] at h
  exact h

theorem d8At_hs8
    {n w : ℕ} (hn : n < 2 ^ 23) (h2 : qmul gArr n n = 0)
    (hc : qmul gArr 128 n = qmul gArr n 128)
    (h2' : qmul gArr (qmul gArr 128 n) (qmul gArr 128 n) = 0)
    (hw : qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsN 8).toArray n) n) = w) :
    D8At (qS 128) (qS w) := by
  refine ⟨hs 8, qS n, hs8_mul_self, qS_mul_self_of_code h2, hs8_comm_qS128,
    qS_comm_of_code hc.symm, ?_, ?_, rank_qS_ne_2158' h2 hn, ?_, ?_⟩
  · rw [rank_hs8]; decide
  · rw [rank_qS128_mul_hs8]; decide
  · rw [qS_mul]; exact rank_qS_ne_2158' h2' (qmul_lt _ _)
  · have h := cosetElt_sq (by decide : IsRank 8) n
    rwa [← liftImgsN_eq, hw, cosetElt] at h

theorem d8At_q1_xs :
    D8At (qS 1) xs := by
  obtain ⟨h22, h3232, h21, h321, hsq, h12, h132, -⟩ := d8Witness_parts
  refine ⟨qS 2, qS 32, qS_mul_self_of_code h22, qS_mul_self_of_code h3232,
    qS_comm_of_code h21, qS_comm_of_code h321, rank_qS_ne_2158' h22 (by norm_num), ?_,
    rank_qS_ne_2158' h3232 (by norm_num), ?_, ?_⟩
  · rw [qS_mul]; exact rank_qS_ne_2158' h12 (qmul_lt _ _)
  · rw [qS_mul]; exact rank_qS_ne_2158' h132 (qmul_lt _ _)
  · rw [qS_mul, qS_mul, hsq, qS_two_pow_22]

theorem d8At_q128_Y2 :
    D8At (qS 128) (qS 1270988) := by
  obtain ⟨-, -, h2c, -, h4, -⟩ := fusionWitness_parts
  obtain ⟨h22, -, -, -, -, -, -, -, -, -, -, -, h2', -⟩ := d8Witness_parts
  exact d8At_hs8 (by norm_num) h22 h2c h2' (by rw [liftImgsN_eq]; exact h4)

theorem d8At_q128_Y3 :
    D8At (qS 128) (qS 7618823) := by
  obtain ⟨-, -, -, -, -, -, h9c, hsq, -⟩ := y3Cert_parts
  obtain ⟨-, -, -, -, -, -, -, h99, -, -, -, -, -, h9', -⟩ := d8Witness_parts
  exact d8At_hs8 (by norm_num) h99 h9c h9' hsq

theorem d8At_q128_cY2 :
    D8At (qS 128) (qS 1255411) := by
  obtain ⟨-, -, h2c, -⟩ := fusionWitness_parts
  obtain ⟨-, -, -, -, -, -, -, -, h31, h3c, hsq, hconj, -, -, h3', hx⟩ := d8Witness_parts
  have h0 : D8At (qS 128) (qS 5449715) := d8At_hs8 (by norm_num) h31 h3c.symm h3' hsq
  refine h0.of_conj (g := qS 2) ?_ ?_
  · rw [qS_comm_of_code h2c.symm, mul_inv_cancel_right]
  · have e1 : qS 2 * qS 1255411 = qS 1255411 * qS 2 * xs := by
      rw [qS_mul, hconj, ← qS_mul, ← qS_mul, qS_two_pow_22]
    have e2 : qS 1255411 * xs = qS 5449715 := by rw [← hx, ← qS_mul, qS_two_pow_22]
    calc qS 2 * qS 1255411 * (qS 2)⁻¹ = qS 1255411 * qS 2 * xs * (qS 2)⁻¹ := by rw [e1]
      _ = qS 1255411 * (xs * qS 2) * (qS 2)⁻¹ := by
        rw [xs_comm (qS_mem 2), mul_assoc (qS 1255411)]
      _ = qS 1255411 * xs := by group
      _ = qS 5449715 := e2

section GenericConj

variable {M : Type*} [Group M]

theorem conj_comp {g g' a b c : M} (h1 : g * a * g⁻¹ = c) (h2 : g' * b * g'⁻¹ = c) :
    g'⁻¹ * g * a * (g'⁻¹ * g)⁻¹ = b := by
  have e : g * a * g⁻¹ = g' * b * g'⁻¹ := h1.trans h2.symm
  calc g'⁻¹ * g * a * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * a * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * b * g'⁻¹) * g' := by rw [e]
    _ = b := by group

theorem conj_mul_of {g a b a' b' : M} (ha : g * a * g⁻¹ = a') (hb : g * b * g⁻¹ = b') :
    g * (a * b) * g⁻¹ = a' * b' := by
  rw [← ha, ← hb]
  group

theorem mul_self_mul_of_comm {a b : M} (ha : a * a = 1) (hb : b * b = 1) (hab : b * a = a * b) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]

end GenericConj

theorem d8At_of_RB
    {s : Sbp} (hs2 : s * s = 1)
    (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2048) (hr' : ((βr (labelS * s)) - 1).rank = 1860) :
    D8At labelS s := by
  rcases frame_two_B (IsConj.refl labelS) hs2 hr hsc with ⟨-, g, hgc, hgw⟩ | ⟨g, hgc, hgw⟩
  · exact d8At_q1_xs.of_conj hgc hgw
  · exfalso
    have e := conj_mul_of hgc hgw
    have h1 : ((βr (labelS * s)) - 1).rank = ((βr (rs 6 * xs)) - 1).rank := by
      rw [← e, rank_conj']
    rw [h1, rank_rs6_mul_xs] at hr'
    exact absurd hr' (by decide)

theorem d8At_of_Y2
    {s : Sbp} (hs2 : s * s = 1)
    (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2048) (hr' : ((βr (labelS * s)) - 1).rank = 2168) :
    D8At labelS s := by
  rcases frame_two_B (IsConj.refl labelS) hs2 hr hsc with ⟨h1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hr'] at h1
    exact absurd h1 (by decide)
  · obtain ⟨-, -, -, -, -, -, h6, -, h8, h9, -⟩ := fusionWitness_parts
    obtain ⟨hy2, hyr⟩ := rank_of_innerTy (k := 2) (by norm_num) h8 (by decide)
    have hcy : qS 1270988 * qS 128 = qS 128 * qS 1270988 := qS_comm_of_code h6
    have hr3 : ((βr (qS 128 * qS 1270988)) - 1).rank = 2168 := by
      rw [qS_mul]
      exact (rank_of_innerTy (k := 3) (qmul_lt _ _) h9 (by decide)).2
    rcases frame_two_B isConj_qS128_labelS hy2 hyr hcy with ⟨h1, -⟩ | ⟨g', hgc', hgw'⟩
    · rw [hr3] at h1
      exact absurd h1 (by decide)
    · exact d8At_q128_Y2.of_conj (conj_comp hgc hgc') (conj_comp hgw hgw')

theorem d8At_of_cY2
    {s : Sbp} (hs2 : s * s = 1)
    (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2168) (hr' : ((βr (labelS * s)) - 1).rank = 2048) :
    D8At labelS s := by
  have hw2 : labelS * s * (labelS * s) = 1 := mul_self_mul_of_comm labelS_mul_self hs2 hsc
  have hwc : labelS * s * labelS = labelS * (labelS * s) := by rw [mul_assoc, hsc]
  have hls : labelS * (labelS * s) = s := by rw [← mul_assoc, labelS_mul_self, one_mul]
  rcases frame_two_B (IsConj.refl labelS) hw2 hr' hwc with ⟨h1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hls, hr] at h1
    exact absurd h1 (by decide)
  · obtain ⟨-, -, -, -, -, -, -, h7, -, -, h10, h11, -⟩ := fusionWitness_parts
    obtain ⟨hy2, hyr⟩ := rank_of_innerTy (k := 3) (by norm_num) h10 (by decide)
    have hcy : qS 1255411 * qS 128 = qS 128 * qS 1255411 := qS_comm_of_code h7
    have h128 : qS 128 * qS 128 = 1 := mul_self_of_isConj_labelS isConj_qS128_labelS
    obtain ⟨hw2', hwr'⟩ := rank_of_innerTy (k := 2) (qmul_lt _ _) h11 (by decide)
    rw [← qS_mul] at hw2' hwr'
    have hcw : qS 128 * qS 1255411 * qS 128 = qS 128 * (qS 128 * qS 1255411) := by
      rw [mul_assoc, ← hcy]
    have hy : qS 128 * (qS 128 * qS 1255411) = qS 1255411 := by
      rw [← mul_assoc, h128, one_mul]
    rcases frame_two_B isConj_qS128_labelS hw2' hwr' hcw with ⟨h1, -⟩ | ⟨g', hgc', hgw'⟩
    · rw [hy, hyr] at h1
      exact absurd h1 (by decide)
    · have ec := conj_comp hgc hgc'
      have ew := conj_comp hgw hgw'
      refine d8At_q128_cY2.of_conj ec ?_
      have e := conj_mul_of ec ew
      rwa [hls, hy] at e

theorem d8At_of_mem_aSet
    {c : Sbp} (hc : c ∈ aSet) : D8At c (qS 7) :=
    by
  obtain ⟨-, -, -, -, h128, -, h9c, -, hy3, hyc, hy33⟩ := y3Cert_parts
  obtain ⟨g, hg, hge⟩ := mem_jClass_seven_of_innerTy (by norm_num) hy3
  have e7 : g * qS 7618823 * g⁻¹ = qS 7 := by rw [hge]; group
  have hc₀ : g * qS 128 * g⁻¹ ∈ aSet := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) (qS_mem 128)
      rwa [inv_inv] at h
    · exact conj_mem_jClass hg (mem_jClass_of_innerTy (by norm_num) h128)
    · rw [← e7, conj_mul_conj', conj_mul_conj', qS_comm_of_code hyc]
    · rw [← e7, conj_mul_conj', rank_conj_inv, qS_mul]
      exact rank_of_innerTy_three (qmul_lt _ _) hy33
  have hD₀ : D8At (g * qS 128 * g⁻¹) (qS 7) :=
    d8At_q128_Y3.of_conj (g := g⁻¹) (by group) (by rw [← e7]; group)
  obtain ⟨k₁, hk₁, hc₁⟩ := exists_conj_of_mem_aSet hc
  obtain ⟨k₂, hk₂, hc₂⟩ := exists_conj_of_mem_aSet hc₀
  have hk7 : qS 7 * k₂ = k₂ * qS 7 := (Subgroup.mem_centralizer_singleton_iff.1 hk₂.1).symm
  have hk7' : qS 7 * k₁ = k₁ * qS 7 := (Subgroup.mem_centralizer_singleton_iff.1 hk₁.1).symm
  refine hD₀.of_conj (g := k₂ * k₁⁻¹) ?_ ?_
  · rw [hc₁, ← hc₂.symm.trans rfl]
    group
  · calc k₂ * k₁⁻¹ * qS 7 * (k₂ * k₁⁻¹)⁻¹ = k₂ * (k₁⁻¹ * (qS 7 * k₁)) * k₂⁻¹ := by group
      _ = qS 7 := by rw [hk7', inv_mul_cancel_left, ← hk7]; group

theorem d8At_of_Y3
    {s : Sbp} (hsQ : s ∈ Qs) (hs2 : s * s = 1)
    (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2168) (hr' : ((βr (labelS * s)) - 1).rank = 2168) :
    D8At labelS s := by
  obtain ⟨g, hg, hgy⟩ := mem_jClass_seven_of_rank hsQ hs2 hr
  have e7 : g * s * g⁻¹ = qS 7 := by rw [hgy]; group
  have hc' : g * labelS * g⁻¹ ∈ aSet := by
    refine ⟨?_, conj_mem_jClass hg labelS_mem_jClass, ?_, ?_⟩
    · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) labelS_mem
      rwa [inv_inv] at h
    · rw [← e7, conj_mul_conj', conj_mul_conj', hsc]
    · rw [← e7, conj_mul_conj', rank_conj_inv, hr']
  exact (d8At_of_mem_aSet hc').of_conj rfl e7

theorem rank_labelS_mul_xs :
    ((βr (labelS * xs)) - 1).rank = 1860 := by
  obtain ⟨j, hj, hjc⟩ := labelS_mem_jClass
  have hjx : j⁻¹ * xs * j = xs := conj_xs hj
  have e : labelS * xs = j⁻¹ * (qS 1 * xs) * j := by
    rw [hjc]
    calc j⁻¹ * qS 1 * j * xs = j⁻¹ * qS 1 * j * (j⁻¹ * xs * j) := by rw [hjx]
      _ = j⁻¹ * (qS 1 * xs) * j := by group
  have hm : j⁻¹ * (qS 1 * xs) * j⁻¹⁻¹ ∈ jClass (qS 1) :=
    conj_mem_jClass (Jbar.op.inv_mem hj) qS_one_mul_xs_mem
  rw [inv_inv] at hm
  rw [e]
  exact rank_of_mem_jClass hm

theorem sEquiv_labelS_mul_xs :
    sEquiv (labelS * xs) =
    (lamW0H : Shat) := by
  rw [map_mul, sEquiv_labelS_eq_cV0, sEquiv_xs]
  apply Subtype.ext
  show ((cV0 : Shat) : Dfull) * xhat = clabel cw0
  rw [coe_cV0, coe_clabelS, clabel_cv0, clabel_cw0]

theorem isConj_lamW0H_of_RA
    {s : Sbp} (hs2 : s * s = 1) (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 1860) (hr' : ((βr (labelS * s)) - 1).rank = 2048) :
    IsConj lamW0H ⟨sEquiv s, sEquiv_mem_vStab hsc⟩ := by
  have hw2 : labelS * s * (labelS * s) = 1 := mul_self_mul_of_comm labelS_mul_self hs2 hsc
  have hwc : labelS * s * labelS = labelS * (labelS * s) := by rw [mul_assoc, hsc]
  have hls : labelS * (labelS * s) = s := by rw [← mul_assoc, labelS_mul_self, one_mul]
  have hxc : xs * labelS = labelS * xs := xs_comm labelS_mem_Qs
  rcases frame_two_B (IsConj.refl labelS) hw2 hr' hwc with ⟨-, g, hgc, hgw⟩ | ⟨g, hgc, hgw⟩
  · rcases frame_two_B (IsConj.refl labelS) xs_mul_self rank_xs hxc with
      ⟨-, g', hgc', hgw'⟩ | ⟨g', hgc', hgw'⟩
    · have ec := conj_comp hgc hgc'
      have ew := conj_comp hgw hgw'
      have es : g'⁻¹ * g * s * (g'⁻¹ * g)⁻¹ = labelS * xs := by
        have e := conj_mul_of ec ew
        rwa [hls] at e
      have hkc : g'⁻¹ * g * labelS = labelS * (g'⁻¹ * g) := by
        calc g'⁻¹ * g * labelS = g'⁻¹ * g * labelS * (g'⁻¹ * g)⁻¹ * (g'⁻¹ * g) := by group
          _ = labelS * (g'⁻¹ * g) := by rw [ec]
      refine (isConj_iff.2 ⟨⟨sEquiv (g'⁻¹ * g), sEquiv_mem_vStab hkc⟩, Subtype.ext ?_⟩).symm
      show sEquiv (g'⁻¹ * g) * sEquiv s * (sEquiv (g'⁻¹ * g))⁻¹ = (lamW0H : Shat)
      rw [← map_conj_eq, es, sEquiv_labelS_mul_xs]
    · exfalso
      have e := conj_mul_of hgc' hgw'
      have h1 : ((βr (labelS * xs)) - 1).rank = ((βr (rs 6 * xs)) - 1).rank := by
        rw [← e, rank_conj']
      rw [rank_labelS_mul_xs, rank_rs6_mul_xs] at h1
      exact absurd h1 (by decide)
  · exfalso
    have e := conj_mul_of hgc hgw
    rw [hls] at e
    have h1 : ((βr s) - 1).rank = ((βr (rs 6 * xs)) - 1).rank := by rw [← e, rank_conj']
    rw [hr, rank_rs6_mul_xs] at h1
    exact absurd h1 (by decide)

theorem mem_commutator_Eam_of_mem
    {a : vStab cv0} (ha : a ∈ commutator (vStab cv0)) :
    vStabEam a ∈ commutator Eam := by
  rw [← map_commutator_vStabEam]
  exact mem_map_of_mem _ ha

theorem dihedral_Eam_of_D8At
    {y : vStab cv0} (hsc : sEquiv.symm (y : Shat) * labelS =
    labelS * sEquiv.symm (y : Shat)) (h : D8At labelS (sEquiv.symm (y : Shat))) :
    ∃ i₁ ∈ commutator Eam, ∃ i₂ ∈ commutator Eam, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
      i₁ * i₂ * (i₁ * i₂) = vStabEam y := by
  obtain ⟨a₁, ha₁, a₂, ha₂, h1, h2, h12⟩ := exists_dihedral_of_D8At h hsc
  have ey : (⟨sEquiv (sEquiv.symm (y : Shat)), sEquiv_mem_vStab hsc⟩ : vStab cv0) = y :=
    Subtype.ext (MulEquiv.apply_symm_apply _ _)
  rw [ey] at h12
  refine ⟨vStabEam a₁, mem_commutator_Eam_of_mem ha₁, vStabEam a₂, mem_commutator_Eam_of_mem ha₂,
    ?_, ?_, ?_⟩
  · rw [← map_mul, h1, map_one]
  · rw [← map_mul, h2, map_one]
  · rw [← map_mul, ← map_mul, h12]

theorem n1Test_of_symm
    {y : vStab cv0}
    (hsQ : sEquiv.symm (y : Shat) ∈ Qs)
    (hsc : sEquiv.symm (y : Shat) * labelS = labelS * sEquiv.symm (y : Shat))
    (hs2 : sEquiv.symm (y : Shat) * sEquiv.symm (y : Shat) = 1)
    (hs1 : sEquiv.symm (y : Shat) ≠ 1) (hsl : sEquiv.symm (y : Shat) ≠ labelS) :
    IsConj (cE' * xhatEam) (vStabEam y) ∨
      ∃ i₁ ∈ commutator Eam, ∃ i₂ ∈ commutator Eam, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
        i₁ * i₂ * (i₁ * i₂) = vStabEam y := by
  obtain ⟨-, hr, -⟩ := native_inner_involution_census labelS_mem_Qs (IsConj.refl labelS)
  rcases hr _ hsQ hsc hs2 hs1 hsl with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_RB hs2 hsc h1 h2))
  · left
    have h := isConj_lamW0H_of_RA hs2 hsc h1 h2
    have ey : (⟨sEquiv (sEquiv.symm (y : Shat)), sEquiv_mem_vStab hsc⟩ : vStab cv0) = y :=
      Subtype.ext (MulEquiv.apply_symm_apply _ _)
    rw [ey] at h
    have h' := vStabEam.toMonoidHom.map_isConj h
    rw [MulEquiv.coe_toMonoidHom, vStabEam_lamW0H] at h'
    exact h'
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_Y2 hs2 hsc h1 h2))
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_cY2 hs2 hsc h1 h2))
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_Y3 hsQ hs2 hsc h1 h2))

theorem symm_ne_one_of_ne_one
    {y : vStab cv0} (hy : y ≠ 1) : sEquiv.symm (y : Shat) ≠ 1 :=
  fun h => hy (Subtype.ext ((sEquiv.symm_apply_eq.1 h).trans (map_one sEquiv)))

theorem symm_ne_labelS_of_ne
    {y : vStab cv0} (hy : y ≠ cV0) :
    sEquiv.symm (y : Shat) ≠ labelS :=
  fun h => hy (Subtype.ext ((sEquiv.symm_apply_eq.1 h).trans sEquiv_labelS_eq_cV0))

theorem n1DihedralTest :
    N1DihedralTest := by
  intro y hyN hy2 hyc
  obtain ⟨y', hy'N, rfl⟩ := hyN
  have hy'2 : y' * y' = 1 := vStabEam.injective (by
    rw [map_mul, map_one]
    exact hy2)
  have hy'c : y' ≠ cV0 := fun h => hyc (by rw [h]; exact vStabEam_cV0)
  by_cases hy'1 : y' = 1
  · right
    refine ⟨1, one_mem _, 1, one_mem _, mul_one 1, mul_one 1, ?_⟩
    rw [hy'1]
    simp
  obtain ⟨hsQ, hsc⟩ := symm_mem_centQ_of_mem_NH hy'N
  have hs2 : sEquiv.symm (y' : Shat) * sEquiv.symm (y' : Shat) = 1 := by
    rw [← map_mul, ← Subgroup.coe_mul, hy'2, Subgroup.coe_one, map_one]
  exact n1Test_of_symm hsQ hsc hs2 (symm_ne_one_of_ne_one hy'1) (symm_ne_labelS_of_ne hy'c)

theorem stroth22_of_involutionsIntoN1
    (hO : CoverOuterLeTwo)
    (h1 : InvolutionsIntoN1) :
    Stroth22 :=
  stroth22_of_N1 hO h1 n1DihedralTest

end CFSG.EvenSmallLie.TwoE6
