module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsSteps

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem gms_card_T_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card T ≤ 4 * f * (2 ^ f) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, -⟩ := h.exists_outHom_of_card_sylow hS2
  obtain ⟨e, Q, hB, -, -⟩ := h.exists_bender_of_card_sylow hS2
  have : Finite (MulAut L) := finite_mulAut L
  obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hB.outer_unitary
  have hout : Nat.card (Outer L) = Nat.gcd 3 (2 ^ f + 1) * (2 * f) := by
    rw [← hDcard, ← hQcard, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
  have hR2 : IsPGroup 2 φ.range :=
    h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hdvd : Nat.card φ.range ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card _
  rw [hout, hk] at hdvd
  have hcop : Nat.Coprime (2 ^ k) (Nat.gcd 3 (2 ^ f + 1)) :=
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
      (by norm_num : Nat.Coprime 2 3)).pow_left k
  have h2 : 2 ^ k ∣ 2 * f := hcop.dvd_of_dvd_mul_left hdvd
  have hf0 : 0 < 2 * f := by have := h.two_le; omega
  have h3 : 2 ^ k ≤ 2 * f := Nat.le_of_dvd hf0 h2
  have hle : szT₁ L T ⊔ zpowers t ≤ T := by
    obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
    exact sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hker : φ.ker = (szT₁ L T ⊔ zpowers t).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, hφ x, mem_subgroupOf]
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    h.card_szT₁_sup_of_card_sylow hS2, hk] at hcard
  rw [← hcard]
  calc 2 * (2 ^ f) ^ 3 * 2 ^ k ≤ 2 * (2 ^ f) ^ 3 * (2 * f) := Nat.mul_le_mul_left _ h3
    _ = 4 * f * (2 ^ f) ^ 3 := by ring

end U3Start

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

theorem gms_mem_szA₁_iff
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
    {z : G} :
    z ∈ szA₁ (szT₁ L T) ↔ z ∈ U ⊔ T ∧ z ^ 2 = 1 ∧ ∀ x ∈ U ⊔ T, x ^ 2 = 1 → z * x = x * z := by
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, -, hA₁2, -⟩ := h.facts_of_card_sylow hS2
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hVU₁ : V ≤ U₁ := le_sup_right.trans hL.sup_le_U₁
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  constructor
  · intro hz
    refine ⟨mem_sup_left (hL.U₁_le (hT₁U₁ (szA₁_le _ hz))), hA₁2 z hz, fun x hx hx2 => ?_⟩
    have hxx : x * x = 1 := by rw [← sq]; exact hx2
    have hU : ∀ u ∈ U₁, z * u = u * z := fun u hu => by
      have h1 := hL.conj_szA₁ u (hL.U₁_le hu) z hz
      calc z * u = (u * z * u⁻¹) * u := by rw [h1]
        _ = u * z := by group
    have htz : z * t = t * z :=
      mem_centralizer_iff.mp h.mem_centralizer_szT₁ z (szA₁_le _ hz)
    rcases hL.muOne_classify hS hx hxx with h1 | h1 | ⟨w', hw'T, hw'2, hw'S, h1⟩
    · exact hU x h1
    · rw [show x = (x * t⁻¹) * t by group]
      calc z * ((x * t⁻¹) * t) = (z * (x * t⁻¹)) * t := by group
        _ = ((x * t⁻¹) * z) * t := by rw [hU _ h1]
        _ = (x * t⁻¹) * (z * t) := by group
        _ = (x * t⁻¹) * (t * z) := by rw [htz]
        _ = (x * t⁻¹) * t * z := by group
    · have hw'z : z * w' = w' * z :=
        ((h.outer_facts_of_card_sylow hS2 hw'T hw'2 hw'S).2.1 z hz).symm
      rw [show x = (x * w'⁻¹) * w' by group]
      calc z * ((x * w'⁻¹) * w') = (z * (x * w'⁻¹)) * w' := by group
        _ = ((x * w'⁻¹) * z) * w' := by rw [hU _ h1]
        _ = (x * w'⁻¹) * (z * w') := by group
        _ = (x * w'⁻¹) * (w' * z) := by rw [hw'z]
        _ = (x * w'⁻¹) * w' * z := by group
  · rintro ⟨hzS, hz2, hzc⟩
    have hzt : z * t = t * z := hzc t (mem_sup_right htT) h.sq_eq_one
    have hzT : z ∈ T := U3C1OuterLevelData.norm_mem_T_of_commute hS hL.isSylowOf.isPGroup
      le_sup_right hzS hzt
    have hzA : z ∈ szA L T t := (h.mem_szA_iff_of_card_sylow hS2).mpr
      ⟨hzT, hz2, fun y hy hy2 => hzc y (mem_sup_right hy) hy2⟩
    obtain ⟨a, ha, e, he, hae⟩ := exists_mul_eq_of_mem_sup_zpowers
      (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁) hzA
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
    · rw [← hae, he1, mul_one]
      exact ha
    · exfalso
      rw [he1] at hae
      obtain ⟨r, hrR, hr2⟩ := hS.ne
      have hrV : r ∈ V := hS.conf.R₂_le hrR
      have hrt : t * r * t⁻¹ = r⁻¹ := hS.conf.inv r hrV
      have hrt2 : (r * t) ^ 2 = 1 := by
        calc (r * t) ^ 2 = r * (t * r * t⁻¹) * (t * t) := by rw [sq]; group
          _ = 1 := by rw [hrt, htt]; group
      have hrtS : r * t ∈ U ⊔ T :=
        mul_mem (mem_sup_left (hL.U₁_le (hVU₁ hrV))) (mem_sup_right htT)
      have hc := hzc (r * t) hrtS hrt2
      rw [← hae] at hc
      have har : a * r = r * a :=
        mem_centralizer_iff.mp (hS.conf.le_centralizer hrV) a (szA₁_le _ ha)
      have hat : a * t = t * a := mem_centralizer_iff.mp h.mem_centralizer_szT₁ a (szA₁_le _ ha)
      have e1 : a * t * (r * t) = a * r⁻¹ := by
        calc a * t * (r * t) = a * (t * r * t⁻¹) * (t * t) := by group
          _ = a * r⁻¹ := by rw [hrt, htt, mul_one]
      have e2 : r * t * (a * t) = r * a := by
        calc r * t * (a * t) = r * (t * a) * t := by group
          _ = r * (a * t) * t := by rw [hat]
          _ = r * a * (t * t) := by group
          _ = r * a := by rw [htt, mul_one]
      rw [e1, e2, ← har] at hc
      have hrr : r⁻¹ = r := mul_left_cancel hc
      apply hr2
      calc r ^ 2 = r * r := sq r
        _ = r * r⁻¹ := by rw [hrr]
        _ = 1 := mul_inv_cancel r

theorem gms_conj_szA₁
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
    {g : G} (hg : g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)) {a : G}
    (ha : a ∈ szA₁ (szT₁ L T)) : g * a * g⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨haS, ha2, hac⟩ := (hL.gms_mem_szA₁_iff hS).mp ha
  refine (hL.gms_mem_szA₁_iff hS).mpr ⟨(mem_normalizer_iff.mp hg a).mp haS, ?_, fun x hx hx2 => ?_⟩
  · calc (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [ha2]; group
  · have hx' : g⁻¹ * x * g ∈ U ⊔ T := (mem_normalizer_iff''.mp hg x).mp hx
    have hx2' : (g⁻¹ * x * g) ^ 2 = 1 := by
      calc (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by rw [sq, sq]; group
        _ = 1 := by rw [hx2]; group
    have e := hac _ hx' hx2'
    calc g * a * g⁻¹ * x = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by rw [e]
      _ = x * (g * a * g⁻¹) := by group

end U3C1OuterLevelData

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem t_mem : t ∈ T := (hW.step.start.start_of_card_sylow hW.step.card_sylow).1

theorem wt_comm : w * t = t * w := mem_centralizer_singleton_iff.mp (hW.step.start.le hW.w_mem)

theorem tw_mem : t * w ∈ T := mul_mem hW.t_mem hW.w_mem

theorem tw_sq : (t * w) ^ 2 = 1 := by
  rw [Commute.mul_pow hW.wt_comm.symm 2, hW.step.start.sq_eq_one, hW.w_sq, one_mul]

theorem tw_not_mem : t * w ∉ szT₁ L T ⊔ zpowers t := fun hm => hW.w_not_mem (by
  rw [show w = t⁻¹ * (t * w) by group]
  exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm)

theorem conj_tw : s * (t * w) * s⁻¹ = t * w := by
  rw [show s * (t * w) * s⁻¹ = (s * t * s⁻¹) * (s * w * s⁻¹) by group, hW.conj_t, hW.conj_w,
    hW.wt_comm]

theorem tw_inv {r : G} (hr : r ∈ V) : t * w * r * (t * w)⁻¹ = r⁻¹ := by
  rw [show t * w * r * (t * w)⁻¹ = t * (w * r * w⁻¹) * t⁻¹ by group, hW.w_cent r hr]
  exact hW.step.conf.inv r hr

theorem conj_szA₁ {a : G} (ha : a ∈ szA₁ (szT₁ L T)) : s * a * s⁻¹ ∈ szA₁ (szT₁ L T) :=
  hW.level.gms_conj_szA₁ hW.step hW.s_mem_normalizer ha

theorem card_T_le : Nat.card T ≤ 4 * f * (2 ^ f) ^ 3 :=
  hW.step.start.gms_card_T_le hW.step.card_sylow

theorem exists_outer_sq_not_mem :
    ∃ b ∈ T, b ∉ szT₁ L T ⊔ zpowers t ∧ b ^ 2 ∉ szT₁ L T ⊔ zpowers t := by
  obtain ⟨b, hbT, b', hb'T, hbS, hb'S, hbb⟩ := hW.idx
  by_contra hno
  push Not at hno
  exact hbb (hW.step.start.mul_inv_mem_of_sq_mem_of_card_sylow hW.step.card_sylow hbT hb'T
    (hno b hbT hbS) (hno b' hb'T hb'S) hbS hb'S)

theorem exists_sq_eq_tw : ∃ g : G, g ^ 2 = t * w := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  obtain ⟨b, hbT, hbS, hb2⟩ := hW.exists_outer_sq_not_mem
  obtain ⟨j, hcS, hc2⟩ := StrongClosureMod.exists_pow_not_mem h.isPGroup hbT hbS
  have hcT : b ^ 2 ^ j ∈ T := pow_mem hbT _
  have hcb : b ^ 2 ^ j ∈ szT₁ L T ⊔ zpowers b := mem_sup_right (pow_mem (mem_zpowers b) _)
  have hM := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hW.tw_mem hcT
    (by rw [hW.tw_sq]; exact one_mem _) hc2 hW.tw_not_mem hcS
  obtain ⟨y, hy, e, he, hye⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one he with he1 | he1
  · rw [he1, mul_one] at hye
    refine h.muOneCent_exists_sq_of_mem hS2 hbT hb2 ?_ hW.tw_sq hW.tw_not_mem
    rw [show t * w = y * b ^ 2 ^ j by rw [hye]; group]
    exact mul_mem (mem_sup_left hy) hcb
  · exfalso
    rw [he1] at hye
    have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy
    have e : w = y * b ^ 2 ^ j := by
      calc w = t⁻¹ * (t * w * (b ^ 2 ^ j)⁻¹) * b ^ 2 ^ j := by group
        _ = t⁻¹ * (y * t) * b ^ 2 ^ j := by rw [hye]
        _ = t⁻¹ * (t * y) * b ^ 2 ^ j := by rw [hyt]
        _ = y * b ^ 2 ^ j := by group
    obtain ⟨g, hg⟩ := h.muOneCent_exists_sq_of_mem hS2 hbT hb2
      (by rw [e]; exact mul_mem (mem_sup_left hy) hcb) hW.w_sq hW.w_not_mem
    exact hW.w_not_sq g hg

end U3C1OuterSwapHigh

theorem u3C1GmsNotConjInput_holds : U3C1GmsNotConjInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW g hg
  obtain ⟨x, hx⟩ := hW.exists_sq_eq_tw
  exact hW.step.muOneCent_conj_ne_sq g x (hg.trans hx.symm)

end CFSG.SeitzReduction.RankOne
