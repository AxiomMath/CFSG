module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.InvolutionsN1Cert
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Dihedral
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueFinal
public import CFSG.Monster.B.GSide.HInnerFusionI3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.GSide CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr globalFusion)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Dihedral

variable {M : Type*} [Group M]

theorem pow_mul_eq_mul_inv_pow {a b : M} (ha : a * a = 1) (hb : b * b = 1) :
    ∀ i : ℕ, (a * b) ^ i * a = a * ((a * b) ^ i)⁻¹
  | 0 => by simp
  | i + 1 => by
    have h1 : (a * b) * a = a * (a * b)⁻¹ := by
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
      simp only [mul_inv_rev, ha', hb', mul_assoc]
    calc (a * b) ^ (i + 1) * a = (a * b) ^ i * ((a * b) * a) := by rw [pow_succ, mul_assoc]
      _ = (a * b) ^ i * a * (a * b)⁻¹ := by rw [h1, mul_assoc]
      _ = a * ((a * b) ^ i)⁻¹ * (a * b)⁻¹ := by rw [pow_mul_eq_mul_inv_pow ha hb i]
      _ = a * ((a * b) ^ (i + 1))⁻¹ := by simp only [pow_succ', mul_inv_rev, mul_assoc]

theorem pow_conj_eq_of_odd {a b : M} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (h : (a * b) ^ (2 * k + 1) = 1) : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  have hc : ((a * b) ^ k)⁻¹ * ((a * b) ^ k)⁻¹ = a * b := by
    rw [← mul_inv_rev, ← pow_add]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ, show k + k + 1 = 2 * k + 1 by ring]
    exact h
  rw [pow_mul_eq_mul_inv_pow ha hb k, mul_assoc, hc, ← mul_assoc, ha, one_mul]

end Dihedral

theorem caseBWord_mem : ((6, 1, 3, caseBWord) : ℕ × ℕ × ℕ × List ℤ) ∈ globalFusion := by
  decide

theorem qS_one_mul_self :
    qS 1 * qS 1 = 1 := qS_mul_self_of_code (by decide)

theorem qS4356_mul_self :
    qS 4356 * qS 4356 = 1 := qS_mul_self_of_code (by decide)

theorem commute_qS4356 :
    Commute (qS 4356) (qS 1) := qS_commute (by decide)

theorem qS854_comm_rs6
    : qS 854 * rs 6 = rs 6 * qS 854 := qS854_mem_bSet.2.2.1

theorem qS854_mul_self
    : qS 854 * qS 854 = 1 := mul_self_of_mem_jClass_seven qS854_mem_bSet.2.1

section Frame

variable {M : Type*} [Group M]

theorem exists_conj_pair_of_relations {r q p t w : M} (hr : r * r = 1) (hq : q * q = 1)
    (hp : p * p = 1) (ht : t * t = 1) (hpr : p * r = r * p) (htq : t * q = q * t)
    (h3 : (q * w⁻¹ * r * w) ^ 3 = 1)
    (h9 : (w⁻¹ * r * w * q * w⁻¹ * p * w * q * (w⁻¹ * r * w) * t) ^ 9 = 1) :
    ∃ s : M, s * r * s⁻¹ = q ∧ s * p * s⁻¹ = t := by
  obtain ⟨A, hA⟩ : ∃ A, A = w⁻¹ * r * w := ⟨_, rfl⟩
  have hr' : r = w * A * w⁻¹ := by rw [hA]; group
  subst hr'
  have e3 : q * w⁻¹ * (w * A * w⁻¹) * w = q * A := by group
  have e9 : w⁻¹ * (w * A * w⁻¹) * w * q * w⁻¹ * p * w * q * (w⁻¹ * (w * A * w⁻¹) * w) * t =
      A * q * w⁻¹ * p * w * q * A * t := by group
  rw [e3] at h3
  rw [e9] at h9
  have hA2 : A * A = 1 := by
    calc A * A = w⁻¹ * (w * A * w⁻¹ * (w * A * w⁻¹)) * w := by group
      _ = 1 := by rw [hr]; group
  have h3' : (A * q) ^ (2 * 1 + 1) = 1 := by
    rw [show 2 * 1 + 1 = 3 from rfl, pow_three]
    rw [pow_three] at h3
    calc A * q * (A * q * (A * q)) = q⁻¹ * (q * A * (q * A * (q * A))) * q := by group
      _ = 1 := by rw [h3]; group
  have hk1 := pow_conj_eq_of_odd hA2 hq h3'
  have hu : (A * q * w⁻¹) * (w * A * w⁻¹) * (A * q * w⁻¹)⁻¹ = q := by
    calc (A * q * w⁻¹) * (w * A * w⁻¹) * (A * q * w⁻¹)⁻¹ =
          (A * q) ^ 1 * A * ((A * q) ^ 1)⁻¹ := by rw [pow_one]; group
      _ = q := hk1
  have hui : (A * q * w⁻¹)⁻¹ = w * q * A := by
    rw [inv_eq_iff_mul_eq_one]
    calc A * q * w⁻¹ * (w * q * A) = A * (q * q) * A := by group
      _ = 1 := by rw [hq, mul_one, hA2]
  set y := (A * q * w⁻¹) * p * (A * q * w⁻¹)⁻¹ with hy
  have hy2 : y * y = 1 := by
    calc y * y = (A * q * w⁻¹) * (p * p) * (A * q * w⁻¹)⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hp]; group
  have hyq : Commute y q := by
    show y * q = q * y
    rw [← hu, hy]
    calc A * q * w⁻¹ * p * (A * q * w⁻¹)⁻¹ * (A * q * w⁻¹ * (w * A * w⁻¹) * (A * q * w⁻¹)⁻¹) =
          A * q * w⁻¹ * (p * (w * A * w⁻¹)) * (A * q * w⁻¹)⁻¹ := by group
      _ = A * q * w⁻¹ * ((w * A * w⁻¹) * p) * (A * q * w⁻¹)⁻¹ := by rw [hpr]
      _ = _ := by group
  have h9' : (y * t) ^ (2 * 4 + 1) = 1 := by
    have e : y * t = A * q * w⁻¹ * p * w * q * A * t := by rw [hy, hui]; group
    rw [e]
    exact h9
  have hk := pow_conj_eq_of_odd hy2 ht h9'
  have hcq : Commute ((y * t) ^ 4) q := (hyq.mul_left htq).pow_left 4
  refine ⟨(y * t) ^ 4 * (A * q * w⁻¹), ?_, ?_⟩
  · calc (y * t) ^ 4 * (A * q * w⁻¹) * (w * A * w⁻¹) * ((y * t) ^ 4 * (A * q * w⁻¹))⁻¹ =
          (y * t) ^ 4 * ((A * q * w⁻¹) * (w * A * w⁻¹) * (A * q * w⁻¹)⁻¹) *
            ((y * t) ^ 4)⁻¹ := by group
      _ = q := by rw [hu, hcq.eq, mul_inv_cancel_right]
  · calc (y * t) ^ 4 * (A * q * w⁻¹) * p * ((y * t) ^ 4 * (A * q * w⁻¹))⁻¹ =
          (y * t) ^ 4 * y * ((y * t) ^ 4)⁻¹ := by rw [hy]; group
      _ = t := hk

end Frame

theorem caseB_frame
    : ∃ t : Sbp, t * rs 6 * t⁻¹ = qS 1 ∧ t * qS 854 * t⁻¹ = qS 4356 := by
  have h3 := fusion_eq caseBWord_mem
  simp only [rs1_eq] at h3
  exact exists_conj_pair_of_relations rs6_mul_self qS_one_mul_self qS854_mul_self
    qS4356_mul_self qS854_comm_rs6 commute_qS4356.eq h3 caseB_pow_nine

open CFSG.Sporadic.Co2Inv (co2_involution_input)

@[expose] def IntoQ
    (y : Sbp) : Prop := ∃ s : Sbp, s * labelS = labelS * s ∧ s * y * s⁻¹ ∈ Qs

theorem intoQ_of_conj
    {y g c q : Sbp} (hc : c ∈ jClass (qS 1)) (hq : q ∈ Qs)
    (hgc : g * labelS * g⁻¹ = c) (hgy : g * y * g⁻¹ = q) : IntoQ y := by
  obtain ⟨j₀, hj₀, hl⟩ := labelS_mem_jClass
  obtain ⟨j₁, hj₁, rfl⟩ := hc
  have hk : j₀⁻¹ * j₁ ∈ Jbar.op := Jbar.op.mul_mem (Jbar.op.inv_mem hj₀) hj₁
  have hkc : j₀⁻¹ * j₁ * (j₁⁻¹ * qS 1 * j₁) * (j₀⁻¹ * j₁)⁻¹ = labelS := by rw [hl]; group
  refine ⟨j₀⁻¹ * j₁ * g, ?_, ?_⟩
  · have e : j₀⁻¹ * j₁ * g * labelS * (j₀⁻¹ * j₁ * g)⁻¹ = labelS := by
      calc _ = j₀⁻¹ * j₁ * (g * labelS * g⁻¹) * (j₀⁻¹ * j₁)⁻¹ := by group
        _ = labelS := by rw [hgc, hkc]
    calc j₀⁻¹ * j₁ * g * labelS =
          j₀⁻¹ * j₁ * g * labelS * (j₀⁻¹ * j₁ * g)⁻¹ * (j₀⁻¹ * j₁ * g) := by group
      _ = labelS * (j₀⁻¹ * j₁ * g) := by rw [e]
  · have e : j₀⁻¹ * j₁ * g * y * (j₀⁻¹ * j₁ * g)⁻¹ =
        ((j₀⁻¹ * j₁)⁻¹)⁻¹ * q * (j₀⁻¹ * j₁)⁻¹ := by rw [← hgy]; group
    rw [e]
    exact conj_mem_Qs (Subgroup.mem_op.1 (Jbar.op.inv_mem hk)) hq

theorem isConj_qS_one_labelS :
    IsConj (qS 1) labelS :=
  (isConj_of_mem_jClass labelS_mem_jClass).symm

theorem exists_conj_y2_ref :
    ∃ g : Sbp, g * qS 1 * g⁻¹ = rs 6 ∧ g * (qS 2 * qS 4) * g⁻¹ = xs := by
  obtain ⟨-, hc, h2, hr, hr'⟩ := orthType_q1 (qS 2 * qS 4) (by simp)
  rcases frame_two_B isConj_qS_one_labelS h2 hr hc with ⟨h, -⟩ | h
  · rw [hr'] at h
    exact absurd h (by decide)
  · exact h

theorem intoQ_of_rank_2048
    {y : Sbp} (hy2 : y * y = 1) (hr : ((βr y) - 1).rank = 2048)
    (hyc : y * labelS = labelS * y) : IntoQ y := by
  rcases frame_two_B (IsConj.refl labelS) hy2 hr hyc with ⟨-, g, hg1, hgx⟩ | ⟨g, hg6, hgx⟩
  · exact intoQ_of_conj (mem_jClass_self _) xs_mem hg1 hgx
  · obtain ⟨g', hg'1, hg'x⟩ := exists_conj_y2_ref
    refine intoQ_of_conj (g := g'⁻¹ * g) (mem_jClass_self _)
      (orthType_q1 (qS 2 * qS 4) (by simp)).1 ?_ ?_
    · calc g'⁻¹ * g * labelS * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * labelS * g⁻¹) * g' := by group
        _ = qS 1 := by rw [hg6, ← hg'1]; group
    · calc g'⁻¹ * g * y * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * y * g⁻¹) * g' := by group
        _ = qS 2 * qS 4 := by rw [hgx, ← hg'x]; group

theorem intoQ_of_labelS_mul
    {y : Sbp} (h : IntoQ (labelS * y)) : IntoQ y := by
  obtain ⟨s, hs, hq⟩ := h
  refine ⟨s, hs, ?_⟩
  have e : s * y * s⁻¹ = labelS * (s * (labelS * y) * s⁻¹) := by
    calc s * y * s⁻¹ = labelS * labelS * (s * y * s⁻¹) := by rw [labelS_mul_self, one_mul]
      _ = labelS * (labelS * s) * y * s⁻¹ := by group
      _ = labelS * (s * labelS) * y * s⁻¹ := by rw [hs]
      _ = _ := by group
  rw [e]
  exact Qs.mul_mem labelS_mem_Qs hq


theorem intoQ_caseB
    {y g c₂ : Sbp} (hJ : c₂.unop ∈ Jbar) (hQ : c₂ ∉ Qs)
    (hc₂l : IsConj c₂ labelS) (hc₂7 : c₂ * qS 7 = qS 7 * c₂)
    (hr₂ : ((βr (c₂ * qS 7)) - 1).rank = 2168) (hgl : g * labelS * g⁻¹ = c₂)
    (hgy : g * y * g⁻¹ = qS 7) : IntoQ y := by
  obtain ⟨i, hi, hci⟩ := exists_jClass_rs hJ (mul_self_of_isConj_labelS hc₂l) hQ
  have hi6 : i = 6 := by
    have := rank_beta_conj (isConj_of_mem_jClass hci)
    rw [rank_of_isConj_labelS hc₂l, rank_rs (by simp only [Finset.mem_Icc] at hi; omega)] at this
    exact rs_rank_eq_1860 hi this.symm
  subst hi6
  obtain ⟨g₆, hg₆, hgc⟩ := hci
  have e6 : g₆ * c₂ * g₆⁻¹ = rs 6 := by rw [hgc]; group
  have hq : g₆ * qS 7 * g₆⁻¹ ∈ bSet := by
    refine mem_bSet_of_rank ?_ (conj_mem_jClass hg₆ (mem_jClass_self _)) ?_ ?_
    · have h := conj_mem_Qs (g := g₆⁻¹) (Jbar.op.inv_mem hg₆) (qS_mem 7)
      rwa [inv_inv] at h
    · rw [← e6, conj_mul_conj', conj_mul_conj', hc₂7]
    · rw [← e6, conj_mul_conj', rank_conj_inv, hr₂]
  obtain ⟨k, hk, hkq⟩ := exists_conj_of_mem_bSet hq
  have hk6 : k * rs 6 = rs 6 * k := Subgroup.mem_centralizer_singleton_iff.1 hk.1
  obtain ⟨t, ht6, ht854⟩ := caseB_frame
  refine intoQ_of_conj (g := t * k⁻¹ * g₆ * g) (mem_jClass_self (qS 1)) (qS_mem 4356) ?_ ?_
  · calc t * k⁻¹ * g₆ * g * labelS * (t * k⁻¹ * g₆ * g)⁻¹ =
          t * k⁻¹ * (g₆ * (g * labelS * g⁻¹) * g₆⁻¹) * k * t⁻¹ := by group
      _ = t * (k⁻¹ * (rs 6 * k)) * t⁻¹ := by rw [hgl, e6]; group
      _ = t * rs 6 * t⁻¹ := by rw [← hk6]; group
      _ = qS 1 := ht6
  · calc t * k⁻¹ * g₆ * g * y * (t * k⁻¹ * g₆ * g)⁻¹ =
          t * k⁻¹ * (g₆ * (g * y * g⁻¹) * g₆⁻¹) * k * t⁻¹ := by group
      _ = t * qS 854 * t⁻¹ := by rw [hgy, hkq]; group
      _ = qS 4356 := ht854

theorem intoQ_of_rank_pair
    {y : Sbp} (hy2 : y * y = 1) (hcy : y * labelS = labelS * y)
    (hry : ((βr y) - 1).rank = 2168) (hrcy : ((βr (labelS * y)) - 1).rank = 2168) :
    IntoQ y := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 (isConj_qS_seven_of_rank hy2 hry)
  have hc₁l : IsConj (g₁ * labelS * g₁⁻¹) labelS := isConj_iff.2 ⟨g₁⁻¹, by group⟩
  have hc₁7 : g₁ * labelS * g₁⁻¹ * qS 7 = qS 7 * (g₁ * labelS * g₁⁻¹) := by
    rw [← hg₁, conj_mul_conj', conj_mul_conj', hcy]
  have hr₁ : ((βr (g₁ * labelS * g₁⁻¹ * qS 7)) - 1).rank = 2168 := by
    rw [← hg₁, conj_mul_conj', rank_conj_inv, hrcy]
  have hc₁4 : (g₁ * labelS * g₁⁻¹) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, mul_self_of_isConj_labelS hc₁l, one_mul]
  obtain ⟨h, hh7, hJ⟩ := exists_conj_into_Jbar_q7 hc₁7 hc₁4
  have e7 : h * qS 7 * h⁻¹ = qS 7 := by rw [hh7]; group
  have hgl : h * g₁ * labelS * (h * g₁)⁻¹ = h * (g₁ * labelS * g₁⁻¹) * h⁻¹ := by group
  have hgy : h * g₁ * y * (h * g₁)⁻¹ = qS 7 := by
    calc h * g₁ * y * (h * g₁)⁻¹ = h * (g₁ * y * g₁⁻¹) * h⁻¹ := by group
      _ = qS 7 := by rw [hg₁, e7]
  have hc₂l : IsConj (h * (g₁ * labelS * g₁⁻¹) * h⁻¹) labelS :=
    (isConj_iff.2 ⟨h⁻¹, by group⟩).trans hc₁l
  have hc₂7 : h * (g₁ * labelS * g₁⁻¹) * h⁻¹ * qS 7 = qS 7 * (h * (g₁ * labelS * g₁⁻¹) * h⁻¹) := by
    rw [← e7, conj_mul_conj', conj_mul_conj', hc₁7]
  have hr₂ : ((βr (h * (g₁ * labelS * g₁⁻¹) * h⁻¹ * qS 7)) - 1).rank = 2168 := by
    rw [← e7, conj_mul_conj', rank_conj_inv, hr₁]
  by_cases hQ : h * (g₁ * labelS * g₁⁻¹) * h⁻¹ ∈ Qs
  · exact intoQ_of_conj (CFSG.Monster.B.CTIB.mem_jClass_of_isConj_labelS hQ hc₂l) (qS_mem 7)
      hgl hgy
  · exact intoQ_caseB hJ hQ hc₂l hc₂7 hr₂ hgl hgy


theorem intoQ_one
    : IntoQ 1 := ⟨1, by group, by simp⟩

theorem intoQ_labelS
    : IntoQ labelS := ⟨1, by group, by simpa using labelS_mem_Qs⟩

theorem intoQ_of_mem_commutator
    {u : vStab cv0} (hu : u ∈ commutator (vStab cv0))
    (hu2 : u * u = 1) : IntoQ (sEquiv.symm (u : Shat)) := by
  set y := sEquiv.symm (u : Shat) with hy
  have hy2 : y * y = 1 := mul_self_symm hu2
  have hyc : y * labelS = labelS * y := commute_labelS_of_mem u
  have hrk : rkH u = ((βr y) - 1).rank := rfl
  have hcy : rkH (cV0 * u) = ((βr (labelS * y)) - 1).rank := rkH_cV0_mul u
  have hw2 : labelS * y * (labelS * y) = 1 := by
    calc labelS * y * (labelS * y) = labelS * (y * labelS) * y := by group
      _ = labelS * (labelS * y) * y := by rw [hyc]
      _ = 1 := by rw [← mul_assoc, labelS_mul_self, one_mul, hy2]
  have hwc : labelS * y * labelS = labelS * (labelS * y) := by rw [mul_assoc, hyc]
  have h2048c : ((βr (labelS * y)) - 1).rank = 2048 → IntoQ y := fun h =>
    intoQ_of_labelS_mul (intoQ_of_rank_2048 hw2 h hwc)
  have h2158 : ((βr y) - 1).rank = 2158 ∨ ((βr (labelS * y)) - 1).rank = 2158 → False :=
    fun h => not_mem_commutator_of_rank_2158 hu2 (by rw [hrk, hcy]; exact h) hu
  by_cases hy1 : y = 1
  · rw [hy1]
    exact intoQ_one
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq, hy2]) hy1
  obtain ⟨i, ⟨hi, hci⟩, -⟩ := four_classes co2_involution_input hord
  have hry := rank_beta_conj hci
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  ·
    have hyl : IsConj y labelS := isConj_labelS_of_rank hord (hry.trans h1)
    by_cases hyc0 : y = labelS
    · rw [hyc0]
      exact intoQ_labelS
    · rcases rank_labelS_mul_of_isConj hyl hyc hyc0 with h | h
      · exact h2048c h
      · exact (h2158 (.inr h)).elim
  · exact intoQ_of_rank_2048 hy2 (hry.trans h0) hyc
  · exact (h2158 (.inl (hry.trans h5))).elim
  ·
    have hry' : ((βr y) - 1).rank = 2168 := hry.trans h3
    have hw1 : labelS * y ≠ 1 := by
      intro h
      have e : y = labelS := by
        calc y = labelS * (labelS * y) := by rw [← mul_assoc, labelS_mul_self, one_mul]
          _ = labelS := by rw [h, mul_one]
      rw [e, GSide.rank_labelS] at hry'
      exact absurd hry' (by decide)
    have hword : orderOf (labelS * y) = 2 := orderOf_eq_prime (by rw [sq, hw2]) hw1
    obtain ⟨j, ⟨hj, hcj⟩, -⟩ := four_classes co2_involution_input hword
    have hrw := rank_beta_conj hcj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    ·
      exfalso
      have hwl : IsConj (labelS * y) labelS := isConj_labelS_of_rank hword (hrw.trans h1)
      have hwne : labelS * y ≠ labelS := by
        intro h
        apply hy1
        calc y = labelS * (labelS * y) := by rw [← mul_assoc, labelS_mul_self, one_mul]
          _ = 1 := by rw [h, labelS_mul_self]
      have hll : labelS * (labelS * y) = y := by rw [← mul_assoc, labelS_mul_self, one_mul]
      rcases rank_labelS_mul_of_isConj hwl hwc hwne with h | h
      · rw [hll, hry'] at h
        exact absurd h (by decide)
      · rw [hll, hry'] at h
        exact absurd h (by decide)
    · exact h2048c (hrw.trans h0)
    · exact (h2158 (.inr (hrw.trans h5))).elim
    · exact intoQ_of_rank_pair hy2 hyc hry' (hrw.trans h3)

theorem exists_conj_mem_NH
    {u : vStab cv0} (hu : u ∈ commutator (vStab cv0)) (hu2 : u * u = 1) :
    ∃ g : vStab cv0, g * u * g⁻¹ ∈ NH := by
  obtain ⟨s, hs, hsQ⟩ := intoQ_of_mem_commutator hu hu2
  have hsC : Commute s labelS := hs
  have hyC : Commute (sEquiv.symm (u : Shat)) labelS := commute_labelS_of_mem u
  have hc : s * sEquiv.symm (u : Shat) * s⁻¹ * labelS =
      labelS * (s * sEquiv.symm (u : Shat) * s⁻¹) :=
    ((hsC.mul_left hyC).mul_left hsC.inv_left).eq
  obtain ⟨n, hn, hne⟩ := exists_mem_NH_of_mem_centQ hsQ hc
  refine ⟨⟨sEquiv s, sEquiv_mem_vStab hs⟩, ?_⟩
  have e : (⟨sEquiv s, sEquiv_mem_vStab hs⟩ : vStab cv0) * u *
      (⟨sEquiv s, sEquiv_mem_vStab hs⟩ : vStab cv0)⁻¹ = n := by
    apply Subtype.ext
    calc (((⟨sEquiv s, sEquiv_mem_vStab hs⟩ : vStab cv0) * u *
          (⟨sEquiv s, sEquiv_mem_vStab hs⟩ : vStab cv0)⁻¹ : vStab cv0) : Shat) =
          sEquiv s * (u : Shat) * (sEquiv s)⁻¹ := rfl
      _ = sEquiv (s * sEquiv.symm (u : Shat) * s⁻¹) := by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      _ = n := hne.symm
  rw [e]
  exact hn

theorem involutionsIntoN1 :
    InvolutionsIntoN1 := by
  intro u hu2
  obtain ⟨v, hv, hvu⟩ : (u : Eam) ∈ (commutator (vStab cv0)).map vStabEam.toMonoidHom := by
    rw [map_commutator_vStabEam]
    exact u.2
  have hv2 : v * v = 1 := by
    have hinj : Function.Injective vStabEam.toMonoidHom := vStabEam.injective
    apply hinj
    rw [map_mul, map_one, hvu, ← Subgroup.coe_mul, hu2, Subgroup.coe_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_NH hv hv2
  have e : vStabEam.toMonoidHom (g * v * g⁻¹) =
      vStabEam.toMonoidHom g * (u : Eam) * (vStabEam.toMonoidHom g)⁻¹ :=
    (map_mul vStabEam.toMonoidHom (g * v) g⁻¹).trans (congrArg₂ (· * ·)
      ((map_mul vStabEam.toMonoidHom g v).trans (congrArg (vStabEam.toMonoidHom g * ·) hvu))
      (map_inv vStabEam.toMonoidHom g))
  have hmem : vStabEam.toMonoidHom (g * v * g⁻¹) ∈ NE := Subgroup.mem_map_of_mem _ hg
  exact ⟨vStabEam.toMonoidHom g, (congrArg (· ∈ NE) e).mp hmem⟩

theorem stroth22
    : Stroth22 := stroth22_of_involutionsIntoN1 coverOuterLeTwo involutionsIntoN1

end CFSG.EvenSmallLie.TwoE6
