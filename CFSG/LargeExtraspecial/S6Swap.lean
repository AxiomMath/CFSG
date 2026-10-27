module

public import CFSG.LargeExtraspecial.S4FiveMain
public import CFSG.LargeExtraspecial.S6Pkg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

section Abstract

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {β : LinearMap.BilinForm (ZMod 2) U}

theorem exists_mem_apply_eq_one (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) U) {a b : U} (hab : β a b = 1)
    {E : Subgroup (U ≃ₗ[ZMod 2] U)} (hEU : E ≤ spPointRadical β a)
    (hcard : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) : ∃ e ∈ E, β b (e b) = 1 := by
  classical
  have : Finite U := Module.finite_of_finite (ZMod 2)
  by_contra hcon
  push Not at hcon
  have h0 : ∀ e ∈ E, β b (e b) = 0 := fun e he => by
    rcases zmod2_eq_zero_or_eq_one (β b (e b)) with h | h
    · exact h
    · exact absurd h (hcon e he)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at hab
    exact zero_ne_one hab
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hperp : ∀ e ∈ E, β a (e b - b) = 0 := fun e he => (hEU he).2.2.2 b
  have hmul : ∀ e ∈ E, ∀ e' ∈ E, β (e' b - b) (e b - b) = 0 ∧
      (e * e') b - b = (e b - b) + (e' b - b) := by
    intro e he e' he'
    have hd' := hperp e' he'
    have h1 : e (e' b - b) = (e' b - b) + β (e' b - b) (e b - b) • a :=
      spPointRadical_apply_of_orthogonal hab (hEU he) hd'
    have h2 : (e * e') b = e b + (e' b - b) + β (e' b - b) (e b - b) • a := by
      rw [LinearEquiv.mul_apply, show e' b = b + (e' b - b) by abel, map_add, h1]
      abel_nf
    have h3' := h0 _ (mul_mem he he')
    rw [h2] at h3'
    simp only [map_add, map_smul, smul_eq_mul, hba, mul_one] at h3'
    rw [h0 e he, show β b (e' b - b) = 0 by rw [map_sub, h0 e' he', hβ.self_eq_zero, sub_zero],
      zero_add, zero_add] at h3'
    refine ⟨h3', ?_⟩
    rw [h2, h3', zero_smul, add_zero]
    abel
  set D := Submodule.span (ZMod 2) {v | ∃ e ∈ E, e b - b = v} with hD
  have hDmem : ∀ v ∈ D, ∃ e ∈ E, e b - b = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨e, he, rfl⟩ := hv
      obtain ⟨e', he', rfl⟩ := hw
      exact ⟨e * e', mul_mem he he', (hmul e he e' he').2⟩
    | smul c v _ hv =>
      obtain ⟨e, he, rfl⟩ := hv
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · exact ⟨1, one_mem _, by simp⟩
      · exact ⟨e, he, by rw [one_smul]⟩
  have haD : a ∉ D := by
    intro haD
    obtain ⟨e, he, hea⟩ := hDmem a haD
    have := h0 e he
    rw [show e b = b + a by rw [← hea]; abel, map_add, hβ.self_eq_zero, zero_add, hba] at this
    exact one_ne_zero this
  set T := D ⊔ (ZMod 2) ∙ a with hT
  have hTiso : T ≤ LinearMap.BilinForm.orthogonal β T := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change β y x = 0
    obtain ⟨d, hd, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨d', hd', c', hc', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hc
    obtain ⟨k', rfl⟩ := Submodule.mem_span_singleton.mp hc'
    obtain ⟨e, he, rfl⟩ := hDmem d hd
    obtain ⟨e', he', rfl⟩ := hDmem d' hd'
    have h1 := (hmul e he e' he').1
    have h2 := hperp e he
    have h3 := hperp e' he'
    have h4 : β (e' b - b) a = 0 := by rw [isAlt_symm hβ, h3]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
      h4, hβ.self_eq_zero, mul_zero, add_zero]
  have hTdim : 2 * finrank (ZMod 2) T ≤ finrank (ZMod 2) U := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd T
    have h2 := Submodule.finrank_mono hTiso
    have h3 := Submodule.finrank_le T
    omega
  have hTD : finrank (ZMod 2) T = finrank (ZMod 2) D + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq D ((ZMod 2) ∙ a)
    have h2 : D ⊓ (ZMod 2) ∙ a = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvD, hva⟩ := Submodule.mem_inf.mp hv
      rcases mem_span_singleton_iff.mp hva with rfl | rfl
      · exact Submodule.zero_mem _
      · exact absurd hvD haD
    rw [h2, finrank_bot, add_zero, finrank_span_singleton ha0] at h1
    exact h1
  have hED : Nat.card E ≤ Nat.card D := by
    refine Nat.card_le_card_of_injective (fun e : E => (⟨(e : U ≃ₗ[ZMod 2] U) b - b,
      Submodule.subset_span ⟨e, e.2, rfl⟩⟩ : D)) ?_
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    have h1 : e b - b = e' b - b := congrArg Subtype.val h
    exact Subtype.ext (spPointRadical_ext hab (hEU he) (hEU he') (sub_left_inj.mp h1))
  have hUa := card_spPointRadical hβ hnd ha0
  have hDcard : Nat.card D = 2 ^ finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hUa] at hcard
  have h4 : 2 ^ (finrank (ZMod 2) U - 1) ≤ 2 ^ (finrank (ZMod 2) D + 1) := by
    calc 2 ^ (finrank (ZMod 2) U - 1) ≤ 2 * Nat.card E := hcard
      _ ≤ 2 * 2 ^ finrank (ZMod 2) D := by rw [← hDcard]; exact Nat.mul_le_mul_left 2 hED
      _ = 2 ^ (finrank (ZMod 2) D + 1) := by ring
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Lbar_eq_mul (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    Nat.card (S.Lbar g) =
      Nat.card (LmodN S g t) * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  set φ := resL haQ ht with hφ
  have hker : φ.ker = (Nbar S g t).subgroupOf (S.Lbar g) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      refine ⟨Lbar_le_Rbar ht x.2, fun v hv => ?_⟩
      have := congrArg (fun e : Vt S g t ≃ₗ[ZMod 2] Vt S g t => ((e ⟨v, hv⟩ : Vt S g t) : S.Qt)) h
      exact this
    · intro h
      refine LinearEquiv.ext fun v => Subtype.ext ?_
      exact h.2 v v.2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, range_resL] at h1
  rw [h1, hker, ← Subgroup.card_map_of_injective (S.Lbar g).subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm]

theorem radBound_of_card_le (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    (h : Nat.card (LmodN S g t) ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 2)) : RadBound S g t := by
  unfold RadBound
  rw [card_Lbar_eq_mul haQ ht]
  exact Nat.mul_le_mul_right _ h

theorem radBound_of_omegaCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ) :
    RadBound S g t := by
  obtain ⟨Q, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
  refine radBound_of_card_le H.conj_mem ht ?_
  rw [hE, card_pointRadical hQ (aV_ne_zero H ht)
    ((hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩)]

theorem radBound_of_tau_not_mem (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t) :
    RadBound S g t := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  refine radBound_of_card_le H.conj_mem ht ?_
  have hle := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hlt : LmodN S g t < spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
    lt_of_le_of_ne hle fun h => hτ (h ▸ spTransvection_mem_U _ _)
  have hU := card_spPointRadical (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
    (aV_ne_zero H ht)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card (LmodN S g t) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp_all
  have hdim : 1 ≤ finrank (ZMod 2) (Vt S g t) - 1 := by
    have := even_finrank_Vt H C ht ht1 hVQ
    have h2 : 0 < finrank (ZMod 2) (Vt S g t) :=
      Nat.pos_of_ne_zero fun h0 => Vt_ne_bot H ht (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨r, hr⟩ := this
    omega
  have e : 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 * 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hU, e] at hk
  have : Nat.card (LmodN S g t) * 2 ≤ 2 * 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
    rw [hk]
    exact Nat.mul_le_mul_left _ hk2
  omega

theorem exists_L0_not_mem_Qa (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    ∃ y : S.M, (y : G) ∈ S.L0 g ∧
      (y : G) * ((h : G) * g) * S.z * ((y : G) * ((h : G) * g))⁻¹ ∉ S.Qa ((h : G) * g) := by
  have hth := mem_Lbar_of_pair H ht hh
  set β := beta H C ht ht1 hVQ with hβdef
  have hab : β (aV ht) (bV hth) = 1 := by
    rcases zmod2_eq_zero_or_eq_one (β (aV ht) (bV hth)) with h0 | h1
    · exact absurd ((beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp h0) (cl_b_not_mem H hb)
    · exact h1
  obtain ⟨e, he, hbe⟩ := exists_mem_apply_eq_one (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) h3 hab (LmodN_le_spPointRadical H C ht ht1 hVQ)
    (card_spPointRadical_le_two_mul H C ht ht1 hVQ)
  obtain ⟨x, hx, hex⟩ := he
  obtain ⟨y, hyL, rfl⟩ := (mem_Lbar S).mp hx
  refine ⟨y, hyL, fun hmem => ?_⟩
  have hbQ := conj_mem_QG' S h.2 H.conj_mem
  have h1 : (e (bV hth) : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
    rw [hex, coe_bV, ρ_cl_conj_z S y hbQ]
    exact S.cl_mem_clSub ⟨conj_mem_QG' S y.2 hbQ, hmem⟩ (conj_mem_QG' S y.2 hbQ)
  rw [← beta_bV_eq_zero_iff H C ht ht1 hVQ hh hth] at h1
  rw [h1] at hbe
  exact zero_ne_one hbe

end CFSG.LargeExtraspecial.S6
