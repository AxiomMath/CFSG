module

public import CFSG.CGT.PushingUpLit.SolKNA.RevPairOf
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18Final
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

section Lemma18


theorem lemma18_eq_form {R T : Subgroup G} {g : G} (hR2 : IsPGroup 2 R) (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hrev : RevPair R g)
    (hF : (frattini ↥R).map R.subtype ≤ R ⊓ Subgroup.centralizer (T : Set G))
    (hCZ : R ⊓ Subgroup.centralizer (T : Set G) ≤ R ⊓ Subgroup.centralizer (R : Set G))
    (hCT : Nonempty (↥(R ⊓ Subgroup.centralizer (T : Set G)) ≃* ↥T))
    (hTel : IsElemAbelian 2 T) (h4 : 4 ≤ Nat.card ↥T)
    (he : (R ⊓ Subgroup.centralizer (T : Set G)).relIndex R = Nat.card ↥T) :
    IsCommSubgroup R := by
  have hinf0 : R ⊓ rightConjugate R g = ⊥ := inf_rightConjugate_eq_bot hTI hg
  have hinf : R ⊓ conjSubgroup g⁻¹ R = ⊥ := hinf0
  have hTR' : T ≤ rightConjugate R g := by rw [hT]; exact inf_le_left
  have hTN : T ≤ Subgroup.normalizer (R : Set G) := by rw [hT]; exact inf_le_right
  have hRT : R ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxT⟩
    have : x ∈ R ⊓ rightConjugate R g := ⟨hxR, hTR' hxT⟩
    rwa [hinf0] at this
  have hNC : R ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.centralizer (T : Set G) :=
    CFSG.ComponentClassification.Asc76.Sec5.inf_normalizer_eq_inf_centralizer hTN hRT
  have hLC : R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) =
      R ⊓ Subgroup.centralizer (T : Set G) :=
    (inf_normalizer_rightConjugate_eq hTI hg hT hT0).trans hNC
  obtain ⟨hNnorm, hΦb₁, hΦb₂, hTZ⟩ := hrev.lemma18_data hR2 hT hLC
  have hT2 : ∀ x ∈ T, x * x = 1 := fun x hx => by
    have := hTel.2 x hx
    rwa [sq] at this
  have hCR : R ⊓ Subgroup.centralizer (T : Set G) ≠ R := by
    intro h
    rw [h, Subgroup.relIndex_self] at he
    omega
  exact lemma18_abelian_eq_final (g := g⁻¹) (Z := ⊤) (Subgroup.mem_top _) le_top hR2
    (isTIIn_of_isTI hTI) (T := T) (C := R ⊓ Subgroup.centralizer (T : Set G))
    (N := (R ⊓ Subgroup.centralizer (T : Set G)) ⊔ T) hT hT0 hinf rfl
    (fun x hx => sq_mem_of_frattini_le hR2 hF hx)
    (fun x hx y hy => comm_mem_of_frattini_le hR2 hF hx hy)
    (fun c hc x hx => (Subgroup.mem_centralizer_iff.mp (hCZ hc).2 x hx).symm) hCT hT2 hCR he rfl
    hNnorm hΦb₁ hΦb₂ hTZ

end Lemma18

section C3


namespace II5

variable {K R T H : Subgroup G} {g : G}

theorem TH_eq_T_final (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hnc : ¬ IsCommSubgroup H) : TH H g = T := by
  have cfgH' := cfgH cfg h5 hHM hnc
  have hTHT := TH_le_T cfg h5 hHM
  have hTHel : IsElemAbelian 2 (TH H g) := isElemAbelian_mono h5.elem_T hTHT
  obtain ⟨-, -, hb3, -, -⟩ := cfgH'.basic
  rcases cfgH'.card_dichotomy hTHel with hd | hd
  · have hrelmul := Subgroup.relIndex_mul_card
      (H := H ⊓ Subgroup.normalizer ((TH H g : Subgroup G) : Set G)) (K := H)
    rw [inf_of_le_left inf_le_left] at hrelmul
    have hle : Nat.card ↥H ≤ Nat.card ↥(TH H g) ^ 2 := by
      calc Nat.card ↥H = (H ⊓ Subgroup.normalizer ((TH H g : Subgroup G) : Set G)).relIndex H *
            Nat.card ↥(H ⊓ Subgroup.normalizer ((TH H g : Subgroup G) : Set G)) := hrelmul.symm
        _ ≤ Nat.card ↥(H ⊓ Subgroup.normalizer ((TH H g : Subgroup G) : Set G)) *
            Nat.card ↥(H ⊓ Subgroup.normalizer ((TH H g : Subgroup G) : Set G)) :=
          Nat.mul_le_mul_right _ hd
        _ = Nat.card ↥(TH H g) ^ 2 := by rw [hb3, sq]
    have hqs : Nat.card ↥T ≤ Nat.card ↥(TH H g) := by
      by_contra hlt
      rw [not_le] at hlt
      have h2 : Nat.card ↥(TH H g) ^ 2 < Nat.card ↥T ^ 2 :=
        Nat.pow_lt_pow_left hlt (by norm_num)
      have h3 := h5.card_H
      omega
    exact Subgroup.eq_of_le_of_card_ge hTHT hqs
  · exfalso
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp cfg.T_isPGroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (isPGroup_TH cfg h5)
    have h1 : 2 * Nat.card ↥(TH H g) ^ 2 = Nat.card ↥T ^ 2 := by
      rw [← hd]
      exact h5.card_H
    rw [hb, ha] at h1
    have e1 : (2 : ℕ) ^ (2 * b + 1) = 2 * (2 ^ b) ^ 2 := by ring
    have e2 : (2 : ℕ) ^ (2 * a) = (2 ^ a) ^ 2 := by ring
    have h2 : (2 : ℕ) ^ (2 * b + 1) = 2 ^ (2 * a) := by rw [e1, e2]; exact h1
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega

theorem revPair (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hnc : ¬ IsCommSubgroup H) : RevPair H g := by
  have hTHT : TH H g = T := TH_eq_T_final cfg h5 hHM hnc
  have cfgH' : NAConfig G H H T g := by
    have := cfgH cfg h5 hHM hnc
    rwa [hTHT] at this
  have hg : g ∉ Subgroup.normalizer (H : Set G) := by
    rw [normalizer_eq cfg h5 hHM]
    exact cfg.g_not
  have hHN : H ⊓ Subgroup.normalizer (T : Set G) = R ⊓ Subgroup.normalizer (T : Set G) :=
    le_antisymm (inf_le_inf_right _ h5.H_le) (le_inf h5.N_le inf_le_right)
  have hcomm : IsCommSubgroup (H ⊓ Subgroup.normalizer (T : Set G)) := fun a ha b hb =>
    h5.N_central a (hHN ▸ ha) b hb.1
  have hNel : IsElemAbelian 2 (H ⊓ Subgroup.normalizer (T : Set G)) :=
    (isElemAbelian_two_iff hcomm).mpr fun a ha => h5.elem_N a (hHN ▸ ha)
  have hNT : Nonempty (↥(H ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T) := by
    obtain ⟨e⟩ := h5.iso
    exact ⟨(MulEquiv.subgroupCongr hHN).trans e⟩
  have hlt : Nat.card ↥T < Nat.card ↥H := by
    have h4 := h5.four_le
    rw [h5.card_H]
    nlinarith
  exact revPair_of_pair (isPGroup cfg h5) (isTI cfg h5 hHM) hg hTHT.symm cfg.T_ne
    (isCommSubgroup_of_isElemAbelian h5.elem_T) cfg.not_isCyclic cfgH'.isTI_T hNel hNT hlt
    h5.card_H.le

theorem isCommSubgroup_H (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    IsCommSubgroup H := by
  have hH2 := isPGroup cfg h5
  by_contra hnc
  have hTHT : TH H g = T := TH_eq_T_final cfg h5 hHM hnc
  obtain ⟨-, -, -, hbC, -⟩ := cfg.basic
  have hg : g ∉ Subgroup.normalizer (H : Set G) := by
    rw [normalizer_eq cfg h5 hHM]
    exact cfg.g_not
  have hHC : H ⊓ Subgroup.centralizer (T : Set G) = R ⊓ Subgroup.normalizer (T : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨h5.H_le hxH, (Subgroup.centralizer_le_normalizer _) hxC⟩
    · intro hx
      have hx' : x ∈ R ⊓ Subgroup.centralizer (T : Set G) := hbC ▸ hx
      exact Subgroup.mem_inf.mpr ⟨h5.N_le hx, (Subgroup.mem_inf.mp hx').2⟩
  have hc1 : (frattini ↥H).map H.subtype ≤ H ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hHC]
    refine CFSG.ComponentClassification.Asc76X.frattini_map_le_of_sq hH2 fun x hx => ?_
    refine h5.omega_le (x ^ 2) (H.pow_mem hx 2) ?_
    rw [← pow_mul]
    exact h5.pow_four x hx
  have hc2 : H ⊓ Subgroup.centralizer (T : Set G) ≤ H ⊓ Subgroup.centralizer (H : Set G) := by
    rw [hHC]
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨h5.N_le hx, Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (h5.N_central x hx h hh).symm⟩
  have hd1 : Nonempty (↥(H ⊓ Subgroup.centralizer (T : Set G)) ≃* ↥T) := by
    obtain ⟨e⟩ := h5.iso
    exact ⟨(MulEquiv.subgroupCongr hHC).trans e⟩
  have he : (H ⊓ Subgroup.centralizer (T : Set G)).relIndex H = Nat.card ↥T := by
    rw [hHC]
    have h1 := Subgroup.relIndex_mul_card (H := R ⊓ Subgroup.normalizer (T : Set G)) (K := H)
    rw [inf_of_le_left h5.N_le, card_N h5, h5.card_H] at h1
    have h4 := h5.four_le
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card ↥T) (h1.trans (sq _))
  exact hnc (lemma18_eq_form hH2 (isTI cfg h5 hHM) hg hTHT.symm cfg.T_ne
    (revPair cfg h5 hHM hnc) hc1 hc2 hd1 h5.elem_T h5.four_le he)

theorem false_of_normal (cfg : NAConfig G K R T g) (h5 : CaseII5 K R T H)
    (hHM : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)) : False :=
  abelian_TI_false (stSetting cfg h5 hHM) (isCommSubgroup_H cfg h5 hHM) (isPGroup cfg h5)
    (not_elemAbelian h5) (not_isCyclic cfg h5)

end II5

end C3

end CFSG.CGT.PushingUpLit.SolKNA
