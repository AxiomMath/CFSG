module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsS1

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.Asc75Lemma31

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G]

@[expose] def MType (V P : Subgroup G) : Prop :=
  ∀ c₁ ∈ P, ∀ c₂ ∈ P, c₁ ∉ V → c₂ ∉ V → c₁ * c₁ = 1 → c₂ * c₂ = 1 → c₁⁻¹ * c₂ ∉ V →
    c₁ * c₂ ≠ c₂ * c₁

namespace Setting310

variable [Finite G] {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem inf_le_V₀_of_elemAbelian {E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian 2 E)
    {e : G} (heE : e ∈ E) (heV : e ∉ R ⊔ T) : E ⊓ (R ⊔ T) ≤ V₀ := by
  intro v hv
  obtain ⟨hvE, hvV⟩ := mem_inf.mp hv
  refine h.P_fixed hP hPC (hEP heE) heV hvV ?_
  have := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨v, hvE⟩)
  simp only [coe_mul] at this
  rw [this]
  group

theorem card_le_eight_of_mType (hm : MType (R ⊔ T) P) {E : Subgroup G} (hEP : E ≤ P)
    (hE : IsElemAbelian 2 E) (hEV : ¬ E ≤ R ⊔ T) : Nat.card E ≤ 8 := by
  obtain ⟨e, heE, heV⟩ := IsConcreteLE.not_le_iff_exists.mp hEV
  have hEV₀ := h.inf_le_V₀_of_elemAbelian hP hPC hEP hE heE heV
  have h4 : Nat.card (E ⊓ (R ⊔ T) : Subgroup G) ≤ 4 :=
    (card_le_of_le hEV₀).trans (le_of_eq h.card_V₀)
  set H := (E ⊓ (R ⊔ T)) ⊔ zpowers e with hH
  have hHE : H ≤ E := sup_le inf_le_left (zpowers_le.mpr heE)
  have hcomm : zpowers e ≤ normalizer ((E ⊓ (R ⊔ T) : Subgroup G) : Set G) :=
    le_normalizer_of_le hE inf_le_left (zpowers_le.mpr heE)
  have hcard := card_sup_mul_card_inf_of_le hcomm
  have he2 : Nat.card (zpowers e) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (hE.2 e heE)
  have hpos : 0 < Nat.card ((zpowers e ⊓ (E ⊓ (R ⊔ T)) : Subgroup G)) := Nat.card_pos
  have hH8 : Nat.card H ≤ 8 := by
    rw [hH, sup_comm]
    have h1 : Nat.card ((zpowers e ⊔ (E ⊓ (R ⊔ T)) : Subgroup G)) * 1 ≤ 2 * 4 :=
      calc _ ≤ Nat.card ((zpowers e ⊔ (E ⊓ (R ⊔ T)) : Subgroup G)) *
            Nat.card ((zpowers e ⊓ (E ⊓ (R ⊔ T)) : Subgroup G)) := Nat.mul_le_mul_left _ hpos
        _ = Nat.card (zpowers e) * Nat.card (E ⊓ (R ⊔ T) : Subgroup G) := hcard
        _ ≤ 2 * 4 := Nat.mul_le_mul he2 h4
    omega
  by_contra hE8
  push Not at hE8
  obtain ⟨e₂, he₂E, he₂H⟩ : ∃ e₂ ∈ E, e₂ ∉ H := by
    by_contra hall
    push Not at hall
    have := card_le_of_le (show E ≤ H from hall)
    omega
  have he₂V : e₂ ∉ R ⊔ T := fun hv => he₂H (mem_sup_left (mem_inf.mpr ⟨he₂E, hv⟩))
  have he₁₂ : e⁻¹ * e₂ ∉ R ⊔ T := fun hv => he₂H (by
    have h1 : e⁻¹ * e₂ ∈ H := mem_sup_left (mem_inf.mpr ⟨mul_mem (inv_mem heE) he₂E, hv⟩)
    have := mul_mem (mem_sup_right (mem_zpowers e)) h1
    rwa [mul_inv_cancel_left] at this)
  have hcomm' := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨e₂, he₂E⟩)
  simp only [coe_mul] at hcomm'
  exact hm e (hEP heE) e₂ (hEP he₂E) heV he₂V (by rw [← sq]; exact hE.2 e heE)
    (by rw [← sq]; exact hE.2 e₂ he₂E) he₁₂ hcomm'

theorem eq_of_elemAbelian_P_of_mType (hm : MType (R ⊔ T) P) {E : Subgroup G} (hEP : E ≤ P)
    (hE : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) : E = R ⊔ T := by
  by_cases hEV : E ≤ R ⊔ T
  · exact eq_of_le_of_card_ge hEV (by rw [h.loc.card, hE16])
  · have := h.card_le_eight_of_mType hP hPC hm hEP hE hEV
    omega

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem eq_of_elemAbelian_of_mType (hm : MType (R ⊔ T) P) {E : Subgroup G}
    (hE : E ≤ P ⊔ zpowers x) (hEe : IsElemAbelian 2 E) (hE16 : Nat.card E = 16) :
    E = R ⊔ T := by
  by_cases hEP : E ≤ P
  · exact h.eq_of_elemAbelian_P_of_mType hP hPC hm hEP hEe hE16
  exfalso
  obtain ⟨u, huE, huP⟩ := IsConcreteLE.not_le_iff_exists.mp hEP
  have hxu : x * u ∈ P := ((outer_mem_sup_iff hx).mp (hE huE)).resolve_left huP
  have hle : P.relIndex E ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := P) hE (by
      rw [outer_relIndex_sup hx]
      norm_num)
    exact h1.trans (le_of_eq (outer_relIndex_sup hx))
  have h8 : 8 ≤ Nat.card (P ⊓ E : Subgroup G) := by
    have h1 := Subgroup.relIndex_mul_card P E
    rw [hE16] at h1
    have h2 : 16 ≤ 2 * Nat.card (P ⊓ E : Subgroup G) := h1 ▸ Nat.mul_le_mul_right _ hle
    omega
  have hXC : P ⊓ E ≤ centralizer ({u} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, (mem_inf.mp he).2⟩ ⟨u, huE⟩))
  have hPEe : IsElemAbelian 2 (P ⊓ E : Subgroup G) := isElemAbelian_of_le hEe inf_le_right
  by_cases hPEV : P ⊓ E ≤ R ⊔ T
  · have := h.outer_card_le_four_V hP hPC hx hxu hPEV hXC
    omega
  obtain ⟨e, heE, heV⟩ := IsConcreteLE.not_le_iff_exists.mp hPEV
  have hPE8 := h.card_le_eight_of_mType hP hPC hm inf_le_left hPEe hPEV
  have hPE8' : Nat.card (P ⊓ E : Subgroup G) = 8 := le_antisymm hPE8 h8
  have hV₀le : V₀ ≤ P ⊓ E := by
    have hEV₀ := h.inf_le_V₀_of_elemAbelian hP hPC inf_le_left hPEe heE heV
    set F := (P ⊓ E) ⊓ (R ⊔ T) with hF
    have hFle : F ≤ P ⊓ E := inf_le_left
    have hidx : 4 ≤ Nat.card F := by
      set H := F ⊔ zpowers e with hH
      have hHle : H ≤ P ⊓ E := sup_le hFle (zpowers_le.mpr heE)
      have hHeq : H = P ⊓ E := by
        by_contra hne
        obtain ⟨e₂, he₂E, he₂H⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hHle hne)
        have he₂V : e₂ ∉ R ⊔ T := fun hv => he₂H (mem_sup_left (mem_inf.mpr ⟨he₂E, hv⟩))
        have he₁₂ : e⁻¹ * e₂ ∉ R ⊔ T := fun hv => he₂H (by
          have h1 : e⁻¹ * e₂ ∈ H :=
            mem_sup_left (mem_inf.mpr ⟨mul_mem (inv_mem heE) he₂E, hv⟩)
          have := mul_mem (mem_sup_right (mem_zpowers e)) h1
          rwa [mul_inv_cancel_left] at this)
        have hcomm' := congrArg Subtype.val (hPEe.1.is_comm.comm ⟨e, heE⟩ ⟨e₂, he₂E⟩)
        simp only [coe_mul] at hcomm'
        exact hm e (mem_inf.mp heE).1 e₂ (mem_inf.mp he₂E).1 heV he₂V
          (by rw [← sq]; exact hPEe.2 e heE) (by rw [← sq]; exact hPEe.2 e₂ he₂E) he₁₂ hcomm'
      have hcomm : zpowers e ≤ normalizer (F : Set G) :=
        le_normalizer_of_le hPEe hFle (zpowers_le.mpr heE)
      have hcard := card_sup_mul_card_inf_of_le hcomm
      rw [sup_comm, ← hH, hHeq, hPE8'] at hcard
      have he2 : Nat.card (zpowers e) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one two_pos (hPEe.2 e heE)
      have hle' : Nat.card ((zpowers e ⊓ F : Subgroup G)) ≤ Nat.card F :=
        card_le_of_le inf_le_right
      by_contra hlt
      push Not at hlt
      have : 8 * Nat.card ((zpowers e ⊓ F : Subgroup G)) ≤ 2 * Nat.card F := by
        rw [hcard]; exact Nat.mul_le_mul_right _ he2
      have hpos : 0 < Nat.card ((zpowers e ⊓ F : Subgroup G)) := Nat.card_pos
      omega
    have hFV₀ : F = V₀ :=
      eq_of_le_of_card_ge hEV₀ (by rw [h.card_V₀]; exact hidx)
    rw [← hFV₀]
    exact hFle
  apply h.outer_not_mem_centralizer_V₀ hx
  rw [mem_centralizer_iff]
  intro w hw
  have hwu : u * w = w * u := (mem_centralizer_singleton_iff.mp (hXC (hV₀le hw))).symm
  have h1 : u * w * u⁻¹ = x * w * x⁻¹ := outer_conj_V₀ hP hx hxu hw
  have h2 : x * w * x⁻¹ = w := by rw [← h1, hwu]; group
  calc w * x = x * w * x⁻¹ * x := by rw [h2]
    _ = x * w := by group

theorem isSylowOf_top_of_mType (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) :
    IsSylowOf 2 (P ⊔ zpowers x) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ := h.outer_isSylowOf_sup hP hPC hx hP64
  obtain ⟨S, hS, hS₁S⟩ := exists_isSylowOf_le le_top hS₁.isPGroup
  have hS₁N : P ⊔ zpowers x ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := hS₁.le
  have hVS₁ : R ⊔ T ≤ P ⊔ zpowers x := (hPC ▸ inf_le_left : R ⊔ T ≤ P).trans le_sup_left
  by_contra hne
  have hlt : P ⊔ zpowers x < S := lt_of_le_of_ne hS₁S fun he => hne (he ▸ hS)
  obtain ⟨n, hn, hnS₁⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hS.isPGroup hlt)
  obtain ⟨hnS, hnN⟩ := mem_inf.mp hn
  have hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    have hS₁n : rightConjugate (P ⊔ zpowers x) n = P ⊔ zpowers x :=
      (rightConjugate_eq_self_iff _ n).mpr hnN
    have hVn : rightConjugate (R ⊔ T) n ≤ P ⊔ zpowers x := by
      rw [← hS₁n]; exact map_mono hVS₁
    exact (rightConjugate_eq_self_iff _ n).mp (h.eq_of_elemAbelian_of_mType hP hPC hx hm hVn
      (isElemAbelian_rightConjugate h.loc.elem n) (by rw [rightConjugate_card, h.loc.card]))
  have hT2 : IsPGroup 2 ((P ⊔ zpowers x) ⊔ zpowers n : Subgroup G) :=
    hS.isPGroup.to_le (sup_le hS₁S (zpowers_le.mpr hnS))
  have heq := hS₁.eq_of_le le_sup_left (sup_le hS₁N (zpowers_le.mpr hnV)) hT2
  exact hnS₁ (heq ▸ mem_sup_right (mem_zpowers n))

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
