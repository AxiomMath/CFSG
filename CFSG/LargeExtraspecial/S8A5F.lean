module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.LargeExtraspecial.S8ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

@[expose] def Timmesfeld83A5Inf : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} →
    S5.Irr S → ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O}
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      OmegaCase H C ht ht1 hVQ → ∀ D : Std H C ht ht1 hVQ, D.m = 2 → D.IsMinus →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      ∀ y ∈ S.Mbar, y * t * y⁻¹ * t = t * (y * t * y⁻¹) → y * t * y⁻¹ ≠ t →
        S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t) = ⊥

@[expose] def Timmesfeld83A5Good : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, TimmesfeldCorBInput →
    CorBListFacts → CentralExtInput.{u} → S5.Irr S → ∀ (H : Hyp4 S g), NoA2 S g →
    ∀ (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ → ∀ D : Std H C ht ht1 hVQ,
      D.m = 2 → D.IsMinus → S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∃ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) ∧ x * t * x⁻¹ ≠ t) →
      ∃ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) ∧ x * t * x⁻¹ ≠ t ∧
        ¬ ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem not_bad_of_good (D : Std H C ht ht1 hVQ) {x σ : S.O} (hxσ : σ = x * t * x⁻¹)
    (hgood : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    ¬ ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  intro hbad
  have h1 := finrank_map_Wt_add (S := S) (g := g) (t := t) σ
  rw [hgood, finrank_bot, add_zero] at h1
  have hle : (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hbad w hw, sub_mem_commSpace _ w⟩
  rw [hgood, le_bot_iff] at hle
  rw [hle, finrank_bot] at h1
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have h3 := D.three_le_finrank
  omega

theorem good_inv (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O}
    (hgood : Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    Vt S g t ⊓ commSpace ((x⁻¹ * t * x⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv, hvσ⟩
  rw [commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1] at hvσ
  obtain ⟨w, hw, rfl⟩ := hvσ
  have hmem : w ∈ Vt S g t ⊓ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine ⟨hw, ?_⟩
    rw [commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
    exact ⟨_, hv, apply_inv_apply_O x w⟩
  rw [hgood, Submodule.mem_bot] at hmem
  rw [hmem, map_zero]
  exact zero_mem _

end CFSG.LargeExtraspecial.S8
