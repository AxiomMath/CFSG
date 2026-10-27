module

public import CFSG.LargeExtraspecial.S8A5LE
public import CFSG.LargeExtraspecial.S8A5K
public import CFSG.LargeExtraspecial.S8A5LD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem pairDataE_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hσt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hσ1 : x * t * x⁻¹ ≠ t)
    (hnb : ¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    (hP1 : ∀ y ∈ S.Mbar, y * t * y⁻¹ * t = t * (y * t * y⁻¹) → y * t * y⁻¹ ≠ t →
      (y * t * y⁻¹ ∈ Epair (S.Lbar g ⊓ Nbar S g t) x ∨
        y * t * y⁻¹ ∈ Epair (S.Lbar g ⊓ Nbar S g t) x⁻¹) →
      S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t) = ⊥) :
    PairDataE S.Mbar (S.Lbar g ⊓ Nbar S g t) (Nbar S g t) t x := by
  have haQ := H.conj_mem
  have hxinv := inv_mem hxM
  have hσM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  obtain ⟨hσ't, -, -⟩ := good_inv_A5 hCE hNo hΩ D hm2 hmin hA7 hxM hσt hσ1 hnb
  have hσ'M : x⁻¹ * t * x⁻¹⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxinv (S.Lbar_le_Mbar g ht)) (inv_mem hxinv)
  have hstep1 := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7
  have hσV := hstep1 _ ⟨hσM, hσt, x, hxM, rfl⟩
  have hσ'V := hstep1 _ ⟨hσ'M, hσ't, x⁻¹, hxinv, rfl⟩
  obtain ⟨hgood, hU⟩ : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∧
      (Wt S g t).map (((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔
        Vt S g t = Vt S g t ⊔ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rcases bad_or_good_A5 hCE hNo hΩ D hm2 hmin hxM rfl hσt hσV with h | h
    · exact absurd h hnb
    · exact h
  have hgood' := good_inv H C ht ht1 hVQ hgood
  obtain ⟨-, hU'⟩ : Vt S g t ⊓ commSpace ((x⁻¹ * t * x⁻¹⁻¹ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∧
      (Wt S g t).map (((x⁻¹ * t * x⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔
        Vt S g t = Vt S g t ⊔ commSpace ((x⁻¹ * t * x⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rcases bad_or_good_A5 hCE hNo hΩ D hm2 hmin hxinv rfl hσ't hσ'V with h | h
    · exact absurd h (not_bad_of_good D rfl hgood')
    · exact h
  have h5 : ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ = t := fun y hy h =>
    conj_eq_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hy h
  have htN := self_mem_Nbar H ht
  have hAM : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α ∈ S.Mbar := fun α hα => S.Lbar_le_Mbar g hα.1
  have hF : ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      α ∈ normalizer (conjSubgroup x (S.Lbar g ⊓ Nbar S g t) : Set S.O) ↔
        α * (x * t * x⁻¹) = x * t * x⁻¹ * α := fun α hα =>
    ⟨fun h => comm_of_mem_normalizer_conj ht htN h5 hxM (hAM α hα) h,
      fun h => mem_normalizer_conj_of_good D hxM rfl hσV hgood hα h⟩
  have hF' : ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      α ∈ normalizer (conjSubgroup x⁻¹ (S.Lbar g ⊓ Nbar S g t) : Set S.O) ↔
        α * (x⁻¹ * t * x⁻¹⁻¹) = x⁻¹ * t * x⁻¹⁻¹ * α := fun α hα =>
    ⟨fun h => comm_of_mem_normalizer_conj ht htN h5 hxinv (hAM α hα) h,
      fun h => mem_normalizer_conj_of_good D hxinv rfl hσ'V hgood' hα h⟩
  exact
    { hAM := fun α hα => hAM α hα
      hAN := inf_le_right
      hsq := fun a ha => mul_self_of_mem_Lbar S haQ ha.1
      htA := ⟨ht, htN⟩
      ht1 := ht1
      hNc := D.hNc
      htN := fun n hn => commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
      hNorm := fun y hyM hyt n hn => by
        obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hyM
        exact conj_mem_Nbar haQ hyt hn
      hP1 := hP1
      hK := fun y hyM hyt a ha hat => conj_Abar_eq_of_inf_A5 D hm2 hmin hyM hyt ha hat
      hxM := hxM
      hσt := hσt
      hσ1 := hσ1
      hF := hF
      hF' := hF'
      h4 := four_mul_card_le_of_good hCE hNo hΩ D hm2 hxM rfl hσt hσV hgood hU
        fun α hα h => (hF α hα).mp h
      h4' := four_mul_card_le_of_good hCE hNo hΩ D hm2 hxinv rfl hσ't hσ'V hgood' hU'
        fun α hα h => (hF' α hα).mp h
      h2 := two_lt_card_of_good hCE hNo hΩ D hm2 hmin hA7 hxM rfl hσt hσV
        fun α hα h => (hF α hα).mpr h
      h2' := two_lt_card_of_good hCE hNo hΩ D hm2 hmin hA7 hxinv rfl hσ't hσ'V
        fun α hα h => (hF' α hα).mpr h }

theorem false_of_A5E (hTI : S9.TIPairInput.{u}) (hBadE : Timmesfeld83A5InfLinBadE.{u})
    (hG1 : Timmesfeld83A5Good.{u}) (hP4 : S9.PGL25ConjResidual.{u})
    (hP5 : S9.PGL25TypeIIResidual.{u}) (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : False := by
  have hw := D.finrank_WV
  have h8 := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
  rw [hm2] at hw
  have hn : 4 < S.width := by omega
  by_cases hiso : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t
  · exact hA7 (S9.Lbar_inf_Nbar_eq_zpowers_of_isolated H hNo C hn ht ht1 hiso)
  push Not at hiso
  obtain ⟨x, hxM, hσt, hσ1, hnb⟩ :=
    hG1 hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hΩ D hm2 hmin hA7 hiso
  obtain ⟨hσ't, hσ'1, hnb'⟩ := good_inv_A5 hCE hNo hΩ D hm2 hmin hA7 hxM hσt hσ1 hnb
  have P := pairDataE_A5 hCE hNo hΩ D hm2 hmin hA7 hxM hσt hσ1 hnb fun y hyM hyc hyne hE => by
    rcases hE with hE | hE
    · exact inf_conj_eq_bot_A5E hP4 hP5 hBadE hCE hIrr hNo hΩ D hm2 hmin hA7 hxM hσt hσ1 hnb
        hyM hyc hyne hE
    · exact inf_conj_eq_bot_A5E hP4 hP5 hBadE hCE hIrr hNo hΩ D hm2 hmin hA7 (inv_mem hxM)
        hσ't hσ'1 hnb' hyM hyc hyne hE
  obtain ⟨y, hyM, hyA, hne⟩ := P.exists_conj_ne hTI
  exact hne (conj_eq_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hyM hyA.1)

theorem false_of_A5_of_corB' (hTI : S9.TIPairInput.{u})
    (hBadE : Timmesfeld83A5InfLinBadE.{u}) (hP4 : S9.PGL25ConjResidual.{u})
    (hP5 : S9.PGL25TypeIIResidual.{u}) (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hA5 : CorBListA5Facts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : False :=
  false_of_A5E hTI hBadE (timmesfeld83A5Good_of_corB hA5) hP4 hP5 hCorB hFacts hCE hIrr hNo hΩ D
    hm2 hmin hA7

end CFSG.LargeExtraspecial.S8
