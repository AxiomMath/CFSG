module

public import CFSG.GH74.GLS.Bg.Pu5.BalADiag
public import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic

public section

namespace CFSG.GH74.GLS.Bg.Pu5.BalA

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Bg.Iii2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barMk_eq_one_iff' {C : Subgroup G} (w : ↥C) :
    TwoThin.barMk ↥C w = 1 ↔ (w : G) ∈ pPrimeCoreOf 2 C := by
  rw [← map_one (TwoThin.barMk ↥C), barMk_eq_iff]
  simp

theorem pRank_eq_of_barImage {C I : Subgroup G} (hIC : I ≤ C) {R : Subgroup (TwoThin.barQ ↥C)}
    (hR : (I.subgroupOf C).map (TwoThin.barMk ↥C) = R) : pRank 2 ↥R = pRank 2 ↥I := by
  let f₀ : ↥I →* TwoThin.barQ ↥C := (TwoThin.barMk ↥C).comp (Subgroup.inclusion hIC)
  let f : ↥I →* ↥f₀.range := f₀.rangeRestrict
  have hsurj : Function.Surjective f := MonoidHom.rangeRestrict_surjective f₀
  have hodd : ¬ 2 ∣ Nat.card f.ker := by
    have hker' : f.ker = f₀.ker := MonoidHom.ker_rangeRestrict f₀
    rw [hker']
    let incl : f₀.ker →* (TwoThin.barMk ↥C).ker :=
      { toFun := fun w => ⟨Subgroup.inclusion hIC w.1, w.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective incl := by
      intro u v h
      have h1 := congrArg (fun z : (TwoThin.barMk ↥C).ker => (z : ↥C)) h
      apply Subtype.ext
      exact Subgroup.inclusion_injective hIC h1
    have hodd' : Odd (Nat.card f₀.ker) :=
      TwoThin.odd_card_ker_barMk.of_dvd_nat (Subgroup.card_dvd_of_injective incl hinj)
    exact fun h => (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)
  have hrange : f₀.range = R := by
    rw [← hR]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Subgroup.inclusion hIC i, i.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← pRank_eq_of_surjective_of_odd_ker f hsurj hodd]
  exact (pRank_eq_of_mulEquiv' (MulEquiv.subgroupCongr hrange)).symm

theorem pRank_img {C K : Subgroup G} (hK : IsPCompIn 2 C K) :
    pRank 2 ↥((K.subgroupOf C).map (TwoThin.barMk ↥C)) = pRank 2 ↥K := by
  have hKC := hK.1
  have hsub : (K.subgroupOf C).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hK).2.1
      Subgroup.IsSubnormal.top
  obtain ⟨e⟩ := TwoThin.hat_equiv_map hsub
  rw [← pRank_eq_of_mulEquiv' e, pRank_hat, pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKC)]

theorem card_center_img {C K : Subgroup G} (hK : IsPCompIn 2 C K) (hr : pRank 2 ↥K ≤ 1) :
    Nat.card (Subgroup.center ↥((K.subgroupOf C).map (TwoThin.barMk ↥C))) = 2 := by
  have hKC := hK.1
  have hsub : (K.subgroupOf C).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hK).2.1
      Subgroup.IsSubnormal.top
  have hO : CFSG.oddCore ↥(K.subgroupOf C) = CFSG.pPrimeCore 2 ↥(K.subgroupOf C) :=
    (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
  have hrank : CFSG.pRank 2 ↥(K.subgroupOf C) ≤ 1 := by
    rw [pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKC)]
    exact hr
  obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf hKC
  have hq : CFSG.IsQuasisimple (↥(K.subgroupOf C) ⧸ CFSG.pPrimeCore 2 ↥(K.subgroupOf C)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e1 (TwoThin.isQuasisimple_hat hK)
  have h2 := card_center_of_rank_one hrank (isQuasisimple_oddCore_quotient hq)
  obtain ⟨e2⟩ := TwoThin.hat_equiv_map hsub
  have e3 : (↥(K.subgroupOf C) ⧸ CFSG.oddCore ↥(K.subgroupOf C)) ≃*
      ↥((K.subgroupOf C).map (TwoThin.barMk ↥C)) :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans e2
  rw [natCard_center_congr e3]
  exact h2

theorem pPrimeCoreOf_le_of_isPCompIn' {X M : Subgroup G} (hM : IsPCompIn 2 X M) :
    pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 X := by
  have hsub : (M.subgroupOf X).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hM).2.1
      Subgroup.IsSubnormal.top
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsub
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hM.1]
  exact Subgroup.map_mono h1

theorem barMk_comm_of_mem_cSec {C K : Subgroup G} (hK : IsPCompIn 2 C K) {z k : G} (hzK : z ∈ K)
    (hz : z ∈ cSec K) (hkK : k ∈ K) :
    TwoThin.barMk ↥C ⟨k, hK.1 hkK⟩ * TwoThin.barMk ↥C ⟨z, hK.1 hzK⟩ =
      TwoThin.barMk ↥C ⟨z, hK.1 hzK⟩ * TwoThin.barMk ↥C ⟨k, hK.1 hkK⟩ := by
  have h1 : ⁅k, z⁆ ∈ pPrimeCoreOf 2 K := hz.2.2 k hkK
  have h2 : ⁅k, z⁆ ∈ pPrimeCoreOf 2 C := pPrimeCoreOf_le_of_isPCompIn' hK h1
  have h3 : TwoThin.barMk ↥C ⁅(⟨k, hK.1 hkK⟩ : ↥C), ⟨z, hK.1 hzK⟩⁆ = 1 :=
    (barMk_eq_one_iff' _).2 h2
  rw [map_commutatorElement] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem swapDiag_injective_of {C K : Subgroup G} (hK : IsPCompIn 2 C K) (hr : pRank 2 ↥K ≤ 1)
    {b z : G} (hbC : b ∈ C) (hzK : z ∈ K) (hz2 : orderOf z = 2) (hzc : z ∈ cSec K)
    (hnz : z * (b⁻¹ * z * b) ∉ pPrimeCoreOf 2 C)
    (hAB : ⁅(K.subgroupOf C).map (TwoThin.barMk ↥C),
        conjSub (TwoThin.barMk ↥C ⟨b, hbC⟩)⁻¹ ((K.subgroupOf C).map (TwoThin.barMk ↥C))⁆ = ⊥) :
    Function.Injective (swapDiag hAB) := by
  have hKC : K ≤ C := hK.1
  have hcard := card_center_img hK hr
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hxc : x ∈ Subgroup.center ↥((K.subgroupOf C).map (TwoThin.barMk ↥C)) :=
    ker_swapDiag_le_center hAB (MonoidHom.mem_ker.mpr hx)
  have hzC : z ∈ C := hKC hzK
  have hzmem : TwoThin.barMk ↥C ⟨z, hzC⟩ ∈ (K.subgroupOf C).map (TwoThin.barMk ↥C) :=
    ⟨⟨z, hzC⟩, hzK, rfl⟩
  have hec : (⟨_, hzmem⟩ : ↥((K.subgroupOf C).map (TwoThin.barMk ↥C))) ∈
      Subgroup.center ↥((K.subgroupOf C).map (TwoThin.barMk ↥C)) := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨k', hk', hk'm⟩ := m.2
    apply Subtype.ext
    show (m : TwoThin.barQ ↥C) * TwoThin.barMk ↥C ⟨z, hzC⟩ =
      TwoThin.barMk ↥C ⟨z, hzC⟩ * (m : TwoThin.barQ ↥C)
    rw [← hk'm]
    exact barMk_comm_of_mem_cSec hK hzK hzc (k := (k' : G)) hk'
  have he1 : (⟨_, hzmem⟩ : ↥((K.subgroupOf C).map (TwoThin.barMk ↥C))) ≠ 1 := by
    intro h
    have h1 : TwoThin.barMk ↥C ⟨z, hzC⟩ = 1 := congrArg Subtype.val h
    have h2 : z ∈ pPrimeCoreOf 2 C := (barMk_eq_one_iff' _).1 h1
    have h3 := odd_orderOf_of_mem_pPrimeCoreOf h2
    rw [hz2] at h3
    exact absurd h3 (by decide)
  have hxe := eq_of_mem_center_of_card_two hcard hxc hec hx1 he1
  have h3 : swapDiag hAB ⟨_, hzmem⟩ = 1 := by
    rw [← hxe]
    exact hx
  rw [swapDiag_apply] at h3
  have h4 : TwoThin.barMk ↥C
      ((⟨z, hzC⟩ : ↥C) * ((⟨b, hbC⟩ : ↥C)⁻¹ * ⟨z, hzC⟩ * ⟨b, hbC⟩)) = 1 := by
    rw [← swapDiag_eq_barMk]
    exact h3
  exact hnz ((barMk_eq_one_iff' _).1 h4)

end CFSG.GH74.GLS.Bg.Pu5.BalA

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Bg.Pu5.BalA
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Lifted

theorem balSwap_of (hBL : BLS) (hDL : DiagLayerS) (h44 : II4_44) : BalSwapS := by
  intro G _ _ hG a b ha hb hab K₁ K₂ hK₁ hK₂ hne hcm T hT hbT z₁ z₂ hz₁ hz₂ hz₁2 hz₂2 hz12 L hL
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two hb
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hab' : a * b = b * a := comm_of_mem_centralizer hab
  have hKC₁ := rr_pcomp hK₁
  have hKC₂ := rr_pcomp hK₂
  have hbK₁ : b ∉ normalizer (K₁ : Set G) := by
    intro hbn
    apply hne
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hbn
    rw [← hcm]
    exact h1.symm
  have hz₁K : z₁ ∈ K₁ := hz₁.2
  have hz₁T : z₁ ∈ T := hz₁.1
  have hz₂K : z₂ ∈ K₂ := hz₂.2
  have hz₂T : z₂ ∈ T := hz₂.1
  have hw : b * z₁ * b⁻¹ = z₂ := by
    have hwT : b * z₁ * b⁻¹ ∈ T := T.mul_mem (T.mul_mem hbT hz₁T) (T.inv_mem hbT)
    have hwK : b * z₁ * b⁻¹ ∈ K₂ := by
      have := conj_mem_cmap' hz₁K b
      rwa [hcm] at this
    have hw2 : orderOf (b * z₁ * b⁻¹) = 2 := by rw [orderOf_conj_eq', hz₁2]
    have hS2 : IsPGroup 2 ↥(T ⊓ K₂) := hT.isPGroup.to_inf_left
    have hQ := h44 G hG a ha K₂ hKC₂ hK₂.2
    refine eq_of_hatMk_eq (K := K₂) (S := T ⊓ K₂) inf_le_right hS2 ⟨hwT, hwK⟩ ⟨hz₂T, hz₂K⟩ ?_
    exact unique_involution_of_sl2or2a7 hQ
      ((orderOf_hatMk inf_le_right hS2 ⟨hwT, hwK⟩).trans hw2)
      ((orderOf_hatMk inf_le_right hS2 ⟨hz₂T, hz₂K⟩).trans hz₂2)
  have hcomm : z₁ * z₂ = z₂ * z₁ := rr_sylow_comm hK₁ hK₂ hne hT z₁ hz₁ z₂ hz₂
  have hz₁sq : z₁ * z₁ = 1 := mul_self_eq_one_of_orderOf_eq_two hz₁2
  have hz₂sq : z₂ * z₂ = 1 := mul_self_eq_one_of_orderOf_eq_two hz₂2
  have hysq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hcomm]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz₁sq, hz₂sq, one_mul]
  have hy1 : z₁ * z₂ ≠ 1 := by
    intro h
    apply hz12
    have : z₂ = z₁⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right hz₁sq]
  have hy2 : orderOf (z₁ * z₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hysq) hy1
  have hbz₂ : b * z₂ * b⁻¹ = z₁ := by
    rw [← hw, hinv]
    calc b * (b * z₁ * b) * b = (b * b) * z₁ * (b * b) := by group
      _ = z₁ := by rw [hbb]; group
  have hyC : z₁ * z₂ ∈ centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : b * (z₁ * z₂) * b⁻¹ = z₁ * z₂ := by
      calc b * (z₁ * z₂) * b⁻¹ = (b * z₁ * b⁻¹) * (b * z₂ * b⁻¹) := by group
        _ = z₂ * z₁ := by rw [hw, hbz₂]
        _ = z₁ * z₂ := hcomm.symm
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hyK : z₁ * z₂ ∈ K₁ ⊔ cmap b K₁ := by
    refine Subgroup.mul_mem_sup hz₁K ?_
    rw [hcm]
    exact hz₂K
  obtain ⟨Λ, hΛdef, hΛc, hΛX, -, -, hel⟩ := hDL G hG a b ha hb hab K₁ hK₁ hbK₁
  have hyΛ : z₁ * z₂ ∈ Λ :=
    hel (z₁ * z₂) ⟨hyK, hyC⟩ ⟨1, by rw [pow_one, pow_two]; exact hysq⟩
      ⟨z₁, hz₁K, 1, one_mem _, by rw [hw, mul_one]⟩
  have hbC : b ∈ centralizer ({a} : Set G) := hab
  have hΛI : Λ = IDiag b K₁ := hΛdef.trans (IDiag_eq hb K₁).symm
  obtain ⟨hAB, hbar⟩ := IG_bar_gen hb hab' hKC₁ hbK₁ hbC
  have hIC : IDiag b K₁ ≤ centralizer ({a} : Set G) :=
    (IDiag_le_sup b K₁).trans (sup_le hKC₁.1 (isPCompIn_conjugate hab' hKC₁).1)
  have hnz : z₁ * (b⁻¹ * z₁ * b) ∉ pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
    intro h
    have e : b⁻¹ * z₁ * b = z₂ := by
      have h1 := hw
      rw [hinv] at h1 ⊢
      exact h1
    rw [e] at h
    have hT1 : z₁ * z₂ ∈ T ⊓ pPrimeCoreOf 2 (centralizer ({a} : Set G)) :=
      ⟨T.mul_mem hz₁T hz₂T, h⟩
    rw [inf_pPrimeCoreOf_eq_bot hT.isPGroup, Subgroup.mem_bot] at hT1
    apply hz12
    have : z₂ = z₁⁻¹ := eq_inv_of_mul_eq_one_right hT1
    rw [this, inv_eq_of_mul_eq_one_right hz₁sq]
  have hzc : z₁ ∈ cSec K₁ := rr_inv_mem_cSec h44 hG hK₁ hz₁K hz₁2
  have hinj := swapDiag_injective_of hKC₁ hK₁.2.le hbC hz₁K hz₁2 hzc hnz hAB
  have hrank : pRank 2 ↥Λ = 1 := by
    rw [hΛI, ← pRank_eq_of_barImage hIC hbar,
      ← pRank_eq_of_mulEquiv' (MonoidHom.ofInjective hinj), pRank_img hKC₁]
    exact hK₁.2
  exact hBL G hG a b ha hb hab Λ hΛc hrank (z₁ * z₂) hyΛ hy2 L hL

end CFSG.GH74.GLS.Bg.Pu5
