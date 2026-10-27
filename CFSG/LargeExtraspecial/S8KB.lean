module

public import CFSG.LargeExtraspecial.S8ThreeA
public import CFSG.LargeExtraspecial.S8ThreeB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

@[expose] def Timmesfeld83PlusGlobal4 : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} →
    S5.Irr S → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → ∀ D : Std H C ht ht1 hVQ, D.m = 4 → ¬ D.IsMinus →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t → S.width ≠ 12 →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ∈ Nbar S g t

@[expose] def Timmesfeld83PlusGlobal3 : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} →
    S5.Irr S → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → ∀ D : Std H C ht ht1 hVQ, D.m = 3 → ¬ D.IsMinus →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t → S.width ≠ 10 →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ∈ Nbar S g t

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem conj_ne_mul_of_not_mem_Nbar (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (y : S.O) : y * τ * y⁻¹ ≠ t * τ := by
  have hk := finrank_Vt_inf_le_two D hfus hsub hxM hxτ hτN
  have hdimV := D.hdim
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hne := ne_conj_mul_of_fix H C ht ht1 hVQ hτV hdimτ (by omega) (y * x)
  intro h
  apply hne
  rw [show y * x * t * (y * x)⁻¹ = y * (x * t * x⁻¹) * y⁻¹ by group, ← hxτ, h]

theorem timmesfeld_8_3_plus (hG4 : Timmesfeld83PlusGlobal4.{u})
    (hG3 : Timmesfeld83PlusGlobal3.{u}) (hCorB : TimmesfeldCorBInput)
    (hFacts : CorBListFacts) (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    (D.m = 3 ∧ ¬ D.IsMinus) ∨ (D.m = 4 ∧ ¬ D.IsMinus) →
      (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
        (D.m = 3 ∧ ¬ D.IsMinus ∧ S.width = 10) ∨ (D.m = 4 ∧ ¬ D.IsMinus ∧ S.width = 12) := by
  intro hm
  by_contra hcon
  push Not at hcon
  obtain ⟨hsub, h10, h12⟩ := hcon
  have hpl : ¬ D.IsMinus := by rcases hm with h | h <;> exact h.2
  have hm3 : 3 ≤ D.m := by rcases hm with h | h <;> omega
  obtain ⟨τ, ⟨-, hτt, x, hxM, rfl⟩, hτN⟩ :=
    step2_exists_not_mem_Nbar hCorB hFacts hCE hIrr hNo hΩ D hA7 hm3
  rcases hm with ⟨h3, -⟩ | ⟨h4, -⟩
  · exact hτN (hG3 hCE hIrr H hNo C ht ht1 hVQ hΩ D h3 hpl hA7 (h10 h3 hpl) hsub x hxM hτt)
  · exact hτN (hG4 hCE hIrr H hNo C ht ht1 hVQ hΩ D h4 hpl hA7 (h12 h4 hpl) hsub x hxM hτt)

end CFSG.LargeExtraspecial.S8
