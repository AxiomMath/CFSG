module

public import CFSG.LargeExtraspecial.S8Four
public import CFSG.LargeExtraspecial.S8ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

variable (S g) in
@[expose] noncomputable def commZ (H : Hyp4 S g) (τ : S.O) (hτt : τ * t = t * τ) :
    Subgroup S.O where
  carrier := {n | n ∈ Nbar S g t ∧ n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb'
    have hc : a * t = t * a := commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar ha)
    have hca : a * t ^ k = t ^ k * a := (Commute.zpow_right hc k).eq
    have hcτ : τ * t ^ k = t ^ k * τ := (Commute.zpow_right hτt k).eq
    have e : a * b * τ * (a * b)⁻¹ * τ⁻¹ = (b * τ * b⁻¹ * τ⁻¹) * (a * τ * a⁻¹ * τ⁻¹) := by
      rw [← hk]
      calc a * b * τ * (a * b)⁻¹ * τ⁻¹ = a * ((b * τ * b⁻¹ * τ⁻¹) * τ) * a⁻¹ * τ⁻¹ := by group
        _ = a * (t ^ k * τ) * a⁻¹ * τ⁻¹ := by rw [← hk]
        _ = t ^ k * (a * τ * a⁻¹ * τ⁻¹) := by rw [← mul_assoc a, hca]; group
    rw [e, ← hk]
    exact mul_mem (zpow_mem (mem_zpowers t) k) ha'
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ha'
    have hc : a * t = t * a := commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar ha)
    have hca : a⁻¹ * t ^ k = t ^ k * a⁻¹ := ((Commute.zpow_right hc k).inv_left).eq
    have e : a⁻¹ * τ * a⁻¹⁻¹ * τ⁻¹ = (t ^ k)⁻¹ := by
      have h1 : a * τ * a⁻¹ = t ^ k * τ := by rw [hk]; group
      have h2 : τ = a⁻¹ * (t ^ k * τ) * a := by rw [← h1]; group
      calc a⁻¹ * τ * a⁻¹⁻¹ * τ⁻¹ = a⁻¹ * τ * a * τ⁻¹ := by rw [inv_inv]
        _ = a⁻¹ * τ * a * (a⁻¹ * (t ^ k * τ) * a)⁻¹ := by rw [← h2]
        _ = a⁻¹ * τ * (t ^ k * τ)⁻¹ * a := by group
        _ = a⁻¹ * (t ^ k)⁻¹ * a := by group
        _ = (t ^ k)⁻¹ := by
          rw [show a⁻¹ * (t ^ k)⁻¹ * a = (a⁻¹ * t ^ k * a)⁻¹ by group, hca]; group
    rw [e]
    exact inv_mem (zpow_mem (mem_zpowers t) k)

theorem comm_mem_zpowers_of_Abar (D : Std H C ht ht1 hVQ) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτt : τ * t = t * τ) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hA : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α * τ * α⁻¹ * τ⁻¹ ∈ zpowers t) :
    ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t := by
  have haQ := H.conj_mem
  have hconj : ∀ r ∈ Rbar S g t, ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      r * α * r⁻¹ ∈ commZ S g H τ hτt := by
    intro r hr α hα
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    have hkt := commute_of_mem_Rbar haQ hr
    refine ⟨conj_mem_Nbar haQ hkt hα.2, ?_⟩
    have hr' : (S.ρ k)⁻¹ ∈ Rbar S g t := inv_mem hr
    have hc0 := comm_mem_Nbar_of_fix H hτM hτt hτV hr'
    obtain ⟨c, hcdef⟩ : ∃ c, c = τ⁻¹ * ((S.ρ k)⁻¹ * τ * S.ρ k) := ⟨_, rfl⟩
    have hcN : c ∈ Nbar S g t := by
      obtain ⟨kτ, rfl⟩ := MonoidHom.mem_range.mp hτM
      have h1 := conj_mem_Nbar haQ (k := kτ⁻¹) (by
        rw [map_inv]
        calc (S.ρ kτ)⁻¹ * t = (S.ρ kτ)⁻¹ * (t * S.ρ kτ) * (S.ρ kτ)⁻¹ := by group
          _ = (S.ρ kτ)⁻¹ * (S.ρ kτ * t) * (S.ρ kτ)⁻¹ := by rw [hτt]
          _ = t * (S.ρ kτ)⁻¹ := by group) hc0
      rw [map_inv, inv_inv] at h1
      rw [hcdef]
      convert h1 using 1
      group
    have hτ' : (S.ρ k)⁻¹ * τ * S.ρ k = τ * c := by rw [hcdef]; group
    have hαc := D.hNc α hα.2 c hcN
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hαc
    have hjτ : τ * t ^ j = t ^ j * τ := (Commute.zpow_right hτt j).eq
    have hτz : τ * (α * c * α⁻¹ * c⁻¹) * τ⁻¹ = α * c * α⁻¹ * c⁻¹ := by
      rw [← hj, hjτ, mul_inv_cancel_right]
    have e1 : α * (τ * c) * α⁻¹ * (τ * c)⁻¹ = (α * τ * α⁻¹ * τ⁻¹) * t ^ j := by
      rw [hj]
      calc α * (τ * c) * α⁻¹ * (τ * c)⁻¹ =
          α * τ * α⁻¹ * (α * c * α⁻¹ * c⁻¹) * τ⁻¹ := by group
        _ = α * τ * α⁻¹ * τ⁻¹ * (τ * (α * c * α⁻¹ * c⁻¹) * τ⁻¹) := by group
        _ = α * τ * α⁻¹ * τ⁻¹ * (α * c * α⁻¹ * c⁻¹) := by rw [hτz]
    have h2 : α * (τ * c) * α⁻¹ * (τ * c)⁻¹ ∈ zpowers t := by
      rw [e1]; exact mul_mem (hA α hα) (zpow_mem (mem_zpowers t) j)
    have e2 : S.ρ k * α * (S.ρ k)⁻¹ * τ * (S.ρ k * α * (S.ρ k)⁻¹)⁻¹ * τ⁻¹ =
        S.ρ k * (α * (τ * c) * α⁻¹ * (τ * c)⁻¹) * (S.ρ k)⁻¹ := by
      rw [← hτ']; group
    rw [e2]
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h2
    rw [← hi, (Commute.zpow_right hkt i).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers t) i
  have hdec := (timmesfeld_6_5_bar H C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb).1
  have hle : Nbar S g t ≤ commZ S g H τ hτt := by
    rw [hdec]
    refine sup_le (fun α hα => ?_) (fun β hβ => ?_)
    · have h1 := hconj 1 (one_mem _) α hα
      simpa using h1
    · have hβ' : (S.ρ D.h)⁻¹ * β * S.ρ D.h ∈ S.Lbar g ⊓ Nbar S g t := by
        refine ⟨(mem_Lbar_mul_iff S D.h g).mp hβ.1, ?_⟩
        have hh' : S.ρ D.h⁻¹ ∈ Rbar S g t := by rw [map_inv]; exact inv_mem D.hh
        have := conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hh') hβ.2
        rwa [map_inv, inv_inv] at this
      have h1 := hconj _ D.hh _ hβ'
      have e : S.ρ D.h * ((S.ρ D.h)⁻¹ * β * S.ρ D.h) * (S.ρ D.h)⁻¹ = β := by group
      rwa [e] at h1
  intro n hn
  exact (hle hn).2

theorem false_of_Abar_comm_mem_zpowers (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hA : ∀ α ∈ S.Lbar g ⊓ Nbar S g t, α * τ * α⁻¹ * τ⁻¹ ∈ zpowers t) : False := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  exact false_of_comm_mem_zpowers D hm3 hfus hsub hxM hxτ hτV hτN
    (comm_mem_zpowers_of_Abar D hτM hτt hτV hA)

end CFSG.LargeExtraspecial.S8
