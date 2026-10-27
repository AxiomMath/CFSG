module

public import CFSG.LargeExtraspecial.S8A5F
public import CFSG.LargeExtraspecial.S8A5G
public import CFSG.LargeExtraspecial.S8A5H
public import CFSG.LargeExtraspecial.S8A5LA
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.LargeExtraspecial.S9PG
public import CFSG.LargeExtraspecial.S9RBMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

@[expose] def Timmesfeld83A5InfLinBadE : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} →
    S5.Irr S → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → ∀ D : Std H C ht ht1 hVQ, D.m = 2 → D.IsMinus →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ≠ t →
      (¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) →
      ∀ y ∈ S.Mbar, y * t * y⁻¹ * t = t * (y * t * y⁻¹) → y * t * y⁻¹ ≠ t →
      y * t * y⁻¹ ∈ Epair (S.Lbar g ⊓ Nbar S g t) x →
      (∀ w ∈ Wt S g t, ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) →
      ∀ τ (hτ : τ ∈ S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t)),
        τ ≠ 1 → ¬ LinCase S g hτ.1.1

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem good_inv_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hσt : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) (hσ1 : x * t * x⁻¹ ≠ t)
    (hnb : ¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    x⁻¹ * t * x⁻¹⁻¹ * t = t * (x⁻¹ * t * x⁻¹⁻¹) ∧ x⁻¹ * t * x⁻¹⁻¹ ≠ t ∧
      ¬ ∀ w ∈ Wt S g t, ((x⁻¹ * t * x⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have hσM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hσV := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 _ ⟨hσM, hσt, x, hxM, rfl⟩
  have hgood : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rcases bad_or_good_A5 hCE hNo hΩ D hm2 hmin hxM rfl hσt hσV with h | h
    · exact absurd h hnb
    · exact h.1
  refine ⟨?_, ?_, not_bad_of_good D rfl (good_inv H C ht ht1 hVQ hgood)⟩
  · rw [inv_inv]
    calc x⁻¹ * t * x * t = x⁻¹ * (t * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * t) * x := by rw [hσt]
      _ = t * (x⁻¹ * t * x) := by group
  · rw [inv_inv]
    intro h
    apply hσ1
    calc x * t * x⁻¹ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [h]
      _ = t := by group

theorem inf_conj_eq_bot_A5E (hP4 : S9.PGL25ConjResidual.{u})
    (hP5 : S9.PGL25TypeIIResidual.{u}) (hBadE : Timmesfeld83A5InfLinBadE.{u})
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O}
    (hxM : x ∈ S.Mbar) (hxc : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) (hxne : x * t * x⁻¹ ≠ t)
    (hxg : ¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {y : S.O} (hyM : y ∈ S.Mbar) (hyc : y * t * y⁻¹ * t = t * (y * t * y⁻¹))
    (hyne : y * t * y⁻¹ ≠ t) (hyE : y * t * y⁻¹ ∈ Epair (S.Lbar g ⊓ Nbar S g t) x) :
    S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t) = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  rw [mem_bot]
  by_contra hτ1
  have haQ := H.conj_mem
  obtain ⟨htA1, htz, hR⟩ := t_mem_A1_of_mem_inf hCE hNo hΩ D hm2 hmin hA7 hyM hyne hτ hτ1
  have hτL : τ ∈ S.Lbar g := hτ.1.1
  have hAτ : S.Lbar g ⊓ Nbar S g τ ≠ zpowers τ := fun h =>
    htz (h ▸ ⟨ht, (mem_A1.mp htA1).2.1⟩)
  rcases timmesfeld_4_5 H hNo C hτL hτ1 with hR' | hL | ⟨hVQτ, hSp | hA6 | hΩτ | hP⟩
  · exact hR hR'
  · by_cases hbad :
        ∀ w ∈ Wt S g t, ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t
    · exact hBadE hCE hIrr H hNo C ht ht1 hVQ hΩ D hm2 hmin hA7 x hxM hxc hxne hxg y hyM hyc
        hyne hyE hbad τ hτ hτ1 hL
    · exact not_linCase_of_good hCE hNo hΩ D hm2 hmin hA7 hyM hyc hbad hτ hL
  ·
    have hX := S9.timmesfeld_9_5 hCE H hNo C hτL hτ1 hVQτ hSp hAτ
    have hτN := self_mem_Nbar H hτL
    have htN := (mem_A1.mp htA1).2.1
    set N := Nbar S g τ with hN
    have hct : (⟨t, htN⟩ : N) ∈ center N := by
      rw [mem_center_iff]
      intro n
      exact Subtype.ext ((mem_A1.mp htA1).2.2 n n.2)
    have hcτ : (⟨τ, hτN⟩ : N) ∈ center N := by
      rw [mem_center_iff]
      intro n
      exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar n.2))
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : center N)).mp hX.2.2.2
    have e1 := hu ⟨_, hct⟩ (fun h => ht1 (congrArg Subtype.val (congrArg Subtype.val h)))
    have e2 := hu ⟨_, hcτ⟩ (fun h => hτ1 (congrArg Subtype.val (congrArg Subtype.val h)))
    have e3 : t = τ := congrArg Subtype.val (congrArg Subtype.val (e1.trans e2.symm))
    exact htz (e3 ▸ mem_zpowers τ)
  · exact S9.timmesfeld_9_2_full hCE hIrr H hNo C hτL hτ1 hVQτ hAτ hA6
  · obtain ⟨Dτ⟩ := Std.nonempty hCE hNo hΩτ
    exact htz (A1_le_zpowers Dτ htA1)
  ·
    have hd := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
    have hw := D.finrank_WV
    exact S9.noPGL25_of_width hP4 hP5 hCE hIrr (by omega) H hNo C hτL hτ1 hVQτ hR hAτ hP

end CFSG.LargeExtraspecial.S8
