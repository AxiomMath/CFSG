module

public import CFSG.CGT.PushingUpLit.C2L.PhaseLGlue
public import CFSG.CGT.PushingUpLit.C2L.SecondBlockData

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement
open T2KSW.Aux

namespace ClassTwoSetup

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
  (hc : ClassTwoSetup G L M T n)
include hc

theorem exists_secondBlockInput
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (h46 : Gomi46Data G) :
    ∃ (D₂ : Subgroup G) (a : G), SecondBlockInput G L M T n (Dc L T) D₂ a := by
  have hTG : IsSylowOf 2 T ⊤ := hc.sec4.sylowG
  have hDD : GomiD T (Dc L T) := hc.gomiD_Dc hWVE h46
  obtain ⟨D₂, hE⟩ := hc.exists_gomiE hWVE hTG hDD
  have hD₂ : GomiD T D₂ := hE.2.1
  have hne : Dc L T ≠ D₂ := hE.2.2.1
  have hTD : T ≤ Subgroup.normalizer (Dc L T : Set G) := by
    rw [hc.normalizer_Dc_eq]
    exact hc.TM
  have hTD₂ : T ≤ Subgroup.normalizer (D₂ : Set G) := by
    have h1 := hE.2.2.2.1
    rw [inf_eq_left.2 hTD] at h1
    exact h1.le.trans inf_le_right
  have hE' : GomiE' T (Dc L T) D₂ := h46.l47 T _ _ hTG hE
  have hTsyl₂ : IsSylowOf 2 T (Subgroup.normalizer (D₂ : Set G)) := hTG.of_le hTD₂ le_top
  obtain ⟨a, haN, hna⟩ := exists_mem_not_mem_normalizer hTsyl₂ hD₂.1.1.not_twoClosed
  have hTsyl : IsSylowOf 2 T (Subgroup.normalizer (Dc L T : Set G)) := by
    rw [hc.normalizer_Dc_eq]
    exact hc.hT
  obtain ⟨g, hgN, hng⟩ := exists_mem_not_mem_normalizer hTsyl hc.gomiH_Dc.not_twoClosed
  have hQ₁ := isOtherSylow_map_conj hTG hTD hgN hng
  have hQ₂ := isOtherSylow_map_conj hTG hTD₂ haN hna
  have hΩ : omegaOneCenterIn T = T ⊓ Subgroup.centralizer (T : Set G) :=
    omegaOneCenterIn_eq_zc (hc.mul_self_of_mem_zc hWVE hTG)
  have hinf₁ : T ⊓ Subgroup.normalizer (Dc L T : Set G) = T := inf_eq_left.2 hTD
  have hinf₂ : T ⊓ Subgroup.normalizer (D₂ : Set G) = T := inf_eq_left.2 hTD₂
  have e1 := h46.l46_two T (Dc L T) D₂ _ hTG hE' hQ₁
  have f1 := h46.l46_index T (Dc L T) D₂ _ hTG hE' hQ₁
  have e2 := h46.l46_two T D₂ (Dc L T) _ hTG hE'.symm hQ₂
  have f2 := h46.l46_index T D₂ (Dc L T) _ hTG hE'.symm hQ₂
  have s1 := h46.l46_sup T (Dc L T) D₂ hTG hE'
  have el1 := h46.l46_one T (Dc L T) D₂ hTG hE'
  have el2 := h46.l46_one T D₂ (Dc L T) hTG hE'.symm
  simp only [hinf₁, hinf₂, omegaOneCenterIn_map_conj, hΩ] at e1 f1 e2 f2 s1
  have hk : (Dc L T).relIndex T = 2 ^ n := by
    have h1 := Subgroup.relIndex_mul_card (H := Dc L T) (K := T)
    rw [inf_of_le_left Dc_le_T, hc.card_T] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hDabel : ∀ x ∈ Dc L T, ∀ y ∈ Dc L T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (el1.1.is_comm.comm (⟨x, hx⟩ : Dc L T) ⟨y, hy⟩)
  have hcardD : Nat.card (Dc L T) = 2 ^ n * Nat.card (zc T) :=
    card_eq_of_sup_relIndex e1 hDabel
      (Subgroup.card_map_of_injective (MulAut.conj g).injective) (f1.trans hk)
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_normalizer_Ec hc.LM hc.MN hc.hT
  have hDVE : blockU L ⊔ Ec L T = Dc L T := by
    refine Subgroup.eq_of_le_of_card_ge
      (sup_le (blockU_le_Dc hc.natBlock hc.LM hc.MN hc.hT) Ec_le_Dc) ?_
    have hzc : zc T = ZT T := ZT_eq.symm
    rw [hcardD, hc.card_blockU_sup_Ec, hzc, hc.card_ZT hWVE]
    exact le_of_eq (by ring)
  refine ⟨D₂, a, ?_⟩
  exact
    { D_def := rfl
      D_eq := hc.oTwoIn_sup_eq_Dc
      E_le := Ec_le_Dc
      card_T_D := hc.card_T
      T_le := hc.hRD
      ne_M := hc.not_normalizer_le_M_of_gomiD hD₂ hne.symm
      D_dec := fun d hd => by
        rw [← hDVE] at hd
        obtain ⟨v, hv, e, he, rfl⟩ := (mem_sup_iff_mul hVn).1 hd
        exact ⟨v, hv, e, he, rfl⟩
      card_D := hcardD
      D₂_le := hD₂.1.2
      T_le_N := hTD₂
      D_elem := el1
      D₂_elem := el2
      sup_eq := s1
      D₂_eq := e2
      relIndex_X := f2
      ti := fun S₁ S₂ h₁ h₂ hne' => (hD₂.inf_eq hTG h₁ h₂ hne').le
      gomiH := hD₂.1.1
      a_mem := haN
      a_not := hna }

end ClassTwoSetup

end CFSG.CGT.PushingUpLit.C2L
