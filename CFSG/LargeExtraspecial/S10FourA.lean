module

public import CFSG.LargeExtraspecial.S10TwoB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] def StronglyClosedL (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∀ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g → S.ρ k * t * (S.ρ k)⁻¹ = t

namespace StronglyClosedL

variable (hSC : StronglyClosedL S g t)
include hSC

theorem conj_eq_conj {h k₁ k₂ : S.M} (h₁ : S.ρ k₁ * t * (S.ρ k₁)⁻¹ ∈ S.Lbar ((h : G) * g))
    (h₂ : S.ρ k₂ * t * (S.ρ k₂)⁻¹ ∈ S.Lbar ((h : G) * g)) :
    S.ρ k₁ * t * (S.ρ k₁)⁻¹ = S.ρ k₂ * t * (S.ρ k₂)⁻¹ := by
  have key : ∀ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((h : G) * g) →
      S.ρ k * t * (S.ρ k)⁻¹ = S.ρ h * t * (S.ρ h)⁻¹ := by
    intro k hk
    rw [mem_Lbar_mul_iff] at hk
    have e : (S.ρ h)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * S.ρ h =
        S.ρ (h⁻¹ * k) * t * (S.ρ (h⁻¹ * k))⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [e] at hk
    have h1 := hSC _ hk
    rw [map_mul, map_inv] at h1
    calc S.ρ k * t * (S.ρ k)⁻¹ = S.ρ h * ((S.ρ h)⁻¹ * S.ρ k * t * ((S.ρ h)⁻¹ * S.ρ k)⁻¹) *
          (S.ρ h)⁻¹ := by group
      _ = S.ρ h * t * (S.ρ h)⁻¹ := by rw [h1]
  rw [key k₁ h₁, key k₂ h₂]

theorem eq_of_mem {h k : S.M} (ht : t ∈ S.Lbar ((h : G) * g))
    (hk : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((h : G) * g)) : S.ρ k * t * (S.ρ k)⁻¹ = t := by
  have h1 : S.ρ 1 * t * (S.ρ 1)⁻¹ ∈ S.Lbar ((h : G) * g) := by
    rw [map_one, one_mul, inv_one, mul_one]
    exact ht
  have := hSC.conj_eq_conj hk h1
  rwa [map_one, one_mul, inv_one, mul_one] at this

theorem commute_of_mem_normalizer (X : Hyp10 S g t) {n : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) : n * t = t * n := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hnM
  have h1 := hSC k ((mem_normalizer_iff.mp hnN t).mp X.ht)
  calc S.ρ k * t = S.ρ k * t * (S.ρ k)⁻¹ * S.ρ k := by group
    _ = t * S.ρ k := by rw [h1]

theorem conj_mem_Abar (X : Hyp10 S g t) {n : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) {x : S.O} (hx : x ∈ S.Lbar g ⊓ Nbar S g t) :
    n * x * n⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hnM
  exact ⟨(mem_normalizer_iff.mp hnN x).mp hx.1,
    conj_mem_Nbar X.haQ (hSC.commute_of_mem_normalizer X hnM hnN) hx.2⟩

end StronglyClosedL

theorem beta_orbV_eq_zero_iff (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (v : Vt S g t) : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk) v = 0 ↔
      (v : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
  set r : Rbar S g t := ⟨S.ρ k, hk⟩
  have hv : v = resV X.haQ t r (resV X.haQ t r⁻¹ v) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [orbV_eq_resV X hk, hv, beta_apply_resV, beta_aV_eq_zero_iff, coe_resV_apply,
    mem_clSub_Qa_mul_iff, ← hv]
  rfl

end CFSG.LargeExtraspecial.S10
