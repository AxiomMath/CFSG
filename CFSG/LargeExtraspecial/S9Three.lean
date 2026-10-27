module

public import CFSG.LargeExtraspecial.S9OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_simple_le_RmodN (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) :
    ∃ X : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t), X ≤ RmodN S g t ∧ IsSimpleGroup X ∧
      S5.NonabelianSylowTwo X := by
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  by_cases h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)
  · have hX := (S45Q.hyp45Q H C).sp ht ht1 hVQ hSp h6
    exact ⟨RmodN S g t, le_rfl, hX.1, hX.2⟩
  · have h4' : finrank (ZMod 2) (Vt S g t) = 4 := by omega
    obtain ⟨-, hS, -, hN⟩ := S45Q.commutator_isometryGroup_four (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) h4'
    refine ⟨_, ?_, hS, hN⟩
    rw [hSp.eq_sp]
    exact commutator_le_self _

theorem false_of_forall_mem_Abar_conj (hCorB : S8.TimmesfeldCorBInput)
    (hFacts : S8.CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (hall : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
      ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧ x * t * x⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    False := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ
    (pairGen_of_spCase H C ht ht1 hVQ hSp) (Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp)
    hh hb
  obtain ⟨X, hXR, hXs, hXn⟩ := exists_simple_le_RmodN H hNo C ht ht1 hVQ hSp
  have hin : S8.conjCentM S t ⊆ Nbar S g t := by
    rintro τ ⟨-, hτt, x, hxM, rfl⟩
    obtain ⟨k, -, hk⟩ := hall x hxM hτt
    exact hk.2
  refine S8.false_of_corB hCorB hFacts hCE hIrr H hNo C
    (four_lt_width_of_spCase H hNo C ht ht1 hVQ hSp hA) ht ht1 hA
    (isPGroup_Nbar_of_spCase hCE H hNo C ht ht1 hVQ hSp) hXR hXs hXn hin
    (fun τ hτ n hn => hNQ.comm n hn τ (hin hτ)) ?_
  rintro τ ⟨-, hτt, x, hxM, rfl⟩ hτne
  obtain ⟨k, hk, hkA⟩ := hall x hxM hτt
  have hkt := commute_of_mem_Rbar haQ hk
  have hkt' : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
    calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
      _ = t * (S.ρ k)⁻¹ := by group
  have e : (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
    calc (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
        ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ * ((S.ρ k)⁻¹ * S.ρ k) := by group
      _ = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by rw [inv_mul_cancel, mul_one]
  have hkxM : (S.ρ k)⁻¹ * x ∈ S.Mbar := S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM
  have hA' : ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := by
    rw [← e]
    refine ⟨(mem_Lbar_mul_iff S k g).mp hkA.1, ?_⟩
    have h1 := conj_mem_Nbar haQ (k := k⁻¹) (by rw [map_inv]; exact hkt') hkA.2
    rwa [map_inv, inv_inv] at h1
  have hne : ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ ≠ t := by
    rw [← e]
    intro he
    apply hτne
    calc x * t * x⁻¹ = S.ρ k * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k) * (S.ρ k)⁻¹ := by group
      _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [he]
      _ = t := by rw [hkt, mul_inv_cancel_right]
  obtain ⟨n, hn, hnτ⟩ := exists_conj_eq_mul_t hCE H hNo C ht ht1 hVQ hSp hkxM hA' hne
  rw [← e] at hnτ
  refine ⟨S.ρ k * n * (S.ρ k)⁻¹, Rbar_le_Mbar (Nbar_le_Rbar (conj_mem_Nbar haQ hkt hn)), ?_⟩
  calc S.ρ k * n * (S.ρ k)⁻¹ * (x * t * x⁻¹) * (S.ρ k * n * (S.ρ k)⁻¹)⁻¹ =
      S.ρ k * (n * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k) * n⁻¹) * (S.ρ k)⁻¹ := by group
    _ = S.ρ k * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hnτ]
    _ = x * t * x⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) := by group
    _ = x * t * x⁻¹ * t := by rw [hkt, mul_inv_cancel_right]

end CFSG.LargeExtraspecial.S9
