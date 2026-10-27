module

public import CFSG.LargeExtraspecial.S14C13Aut
public import CFSG.LargeExtraspecial.S14C13Data
public import CFSG.LargeExtraspecial.S2SixInd
public import CFSG.LargeExtraspecial.S2SixSpInd
public import CFSG.LargeExtraspecial.S14C13Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_resV_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (he : e ∈ RmodN S g t) :
    ∃ r : Rbar S g t, resV haQ t r = e := by
  rw [← range_resV haQ t] at he
  exact he

theorem inner_of_sp {t : S.O} {H : Hyp4 S g} {C : Cons311 S g} {ht : t ∈ S.Lbar g}
    {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (hSp : SpCase H C ht ht1 hVQ) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) (Vt S g t) = 2 * m) {y : Ct S t}
    (hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O)) :
    ∃ r₀ : Rbar S g t, ∀ e : RmodN S g t,
      (autC H.conj_mem y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        resV H.conj_mem t r₀ * e * (resV H.conj_mem t r₀)⁻¹ := by
  let α : S2.SpG (beta H C ht ht1 hVQ) ≃* S2.SpG (beta H C ht ht1 hVQ) :=
    ((MulEquiv.subgroupCongr hSp.eq_sp).symm.trans (autC H.conj_mem y)).trans
      (MulEquiv.subgroupCongr hSp.eq_sp)
  have hαL : ∀ w : S2.SpG (beta H C ht ht1 hVQ),
      (w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ spPointRadical (beta H C ht ht1 hVQ) (aV ht) ↔
        (α w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ spPointRadical (beta H C ht ht1 hVQ) (aV ht) := by
    intro w
    rw [← hSp.LmodN_eq]
    exact (autC_mem_LmodN_iff H.conj_mem hyL ((MulEquiv.subgroupCongr hSp.eq_sp).symm w)).symm
  obtain ⟨e₀, he₀⟩ := S2.sp_timmesfeld_2_6_2_spGroup (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) hm hdim (aV_ne_zero H ht) α hαL
  have he₀R : (e₀ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hSp.eq_sp]
    exact e₀.2
  obtain ⟨r₀, hr₀⟩ := exists_resV_eq H.conj_mem he₀R
  refine ⟨r₀, fun e => ?_⟩
  have h1 := congrArg Subtype.val (he₀ (MulEquiv.subgroupCongr hSp.eq_sp e))
  rw [hr₀]
  simpa only [α, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.subgroupCongr_apply] using h1

theorem cLin_nqRep_autC {t : S.O} [hN : NQHyp S g t] (y : Ct S t)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) (w : Y)
    (v : NQ S g t) :
    cLin y.2 (nqRep S g t hY w v) = nqRep S g t hY
      (MulEquiv.subgroupCongr hY (autC hN.conj_mem y ((MulEquiv.subgroupCongr hY).symm w)))
        (cLin y.2 v) := by
  have hv := nqMk_surjective (S := S) (g := g) (t := t) v
  rcases hv with ⟨n, hn⟩
  rw [← hn]
  have hwR : (w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hY]
    exact w.2
  have hx0 := exists_resV_eq hN.conj_mem hwR
  rcases hx0 with ⟨x, hx⟩
  have hx' : ((MulEquiv.subgroupCongr hY (autC hN.conj_mem y
      ((MulEquiv.subgroupCongr hY).symm w)) : Y) : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
      resV hN.conj_mem t ⟨(y : S.O) * (x : S.O) * (y : S.O)⁻¹,
        conj_mem_Rbar_of_mem_Ct y.2 x.2⟩ := by
    rw [MulEquiv.subgroupCongr_apply, coe_autC, ← resC_mul_resV, hx]
    rfl
  have he : ((cConj y.2 (nConj x n) : Nbar S g t) : S.O) =
      ((nConj ⟨(y : S.O) * (x : S.O) * (y : S.O)⁻¹, conj_mem_Rbar_of_mem_Ct y.2 x.2⟩
        (cConj y.2 n) : Nbar S g t) : S.O) := by
    show (y : S.O) * ((x : S.O) * (n : S.O) * (x : S.O)⁻¹) * (y : S.O)⁻¹ =
      ((y : S.O) * (x : S.O) * (y : S.O)⁻¹) * ((y : S.O) * (n : S.O) * (y : S.O)⁻¹) *
        ((y : S.O) * (x : S.O) * (y : S.O)⁻¹)⁻¹
    group
  calc cLin y.2 (nqRep S g t hY w (nqMk n)) = cLin y.2 (nqMk (nConj x n)) :=
        congrArg _ (nqRep_apply hY hx.symm n)
    _ = nqMk (cConj y.2 (nConj x n)) := rfl
    _ = nqMk (nConj ⟨(y : S.O) * (x : S.O) * (y : S.O)⁻¹, conj_mem_Rbar_of_mem_Ct y.2 x.2⟩
          (cConj y.2 n)) :=
        congrArg nqMk (Subtype.ext he)
    _ = _ := (nqRep_apply hY hx' _).symm

theorem inner_of_omega (hCE : CentralExtInput.{0}) {t : S.O} {c : Config} (hSt : Stage S g t)
    (hocc : c.Occurs S g t) {m : ℕ} (hm : 2 ≤ m) (hΩ' : RNOmega S g t (2 * m))
    (hdimM : ∀ _ : NQHyp S g t, finrank (ZMod 2) (NQ S g t) = 2 ^ (m - 1)) {y : Ct S t}
    (hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O)) :
    ∃ r₀ : Rbar S g t, ∀ e : RmodN S g t,
      (autC hSt.hyp4.conj_mem y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        resV hSt.hyp4.conj_mem t r₀ * e * (resV hSt.hyp4.conj_mem t r₀)⁻¹ := by
  have : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  obtain ⟨Q, hQ, hX, p, p₁, hdimV, hp0, hp, hp₁, hpp, hE, hcomp⟩ :=
    omega_data hCE hSt hocc hΩ'
  let α : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ≃*
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    ((MulEquiv.subgroupCongr hX).symm.trans (autC hSt.hyp4.conj_mem y)).trans
      (MulEquiv.subgroupCongr hX)
  have hαL : ∀ w : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ,
      (w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical Q p ↔
        (α w : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical Q p := by
    intro w
    rw [← hE]
    exact (autC_mem_LmodN_iff hSt.hyp4.conj_mem hyL ((MulEquiv.subgroupCongr hX).symm w)).symm
  have hτ : ∀ (w : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) (v : NQ S g t),
      cEquiv y.2 (nqRep S g t hX w v) = nqRep S g t hX (α w) (cEquiv y.2 v) := by
    intro w v
    exact cLin_nqRep_autC y hX w v
  obtain ⟨e₀, he₀⟩ := S2.timmesfeld_2_6_2_omegaGroup (nqRep S g t hX) hm hdimV hp0 hp hp₁ hpp
    hcomp (hdimM this) α hαL (cEquiv y.2) hτ
  have he₀R : (e₀ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hX]
    exact e₀.2
  obtain ⟨r₀, hr₀⟩ := exists_resV_eq hSt.hyp4.conj_mem he₀R
  refine ⟨r₀, fun e => ?_⟩
  have h1 := congrArg Subtype.val (he₀ (MulEquiv.subgroupCongr hX e))
  rw [hr₀]
  simpa only [α, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.subgroupCongr_apply] using h1

end CFSG.LargeExtraspecial.S14
