module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S4SevenInput
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

@[expose] def PGL25Step4Residual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
      (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), PGL25Case H C ht ht1 hVQ →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) →
      ∀ n ∈ S.Mbar, n ∈ normalizer (S.Lbar g : Set S.O) →
        finrank (ZMod 2) ↥(Vt S g t ⊓ (Vt S g t).map (n : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) ≠ 2

@[expose] def PGL25Step5Residual : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}, CentralExtInput.{u} → S5.Irr S →
    ∀ (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
      (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), PGL25Case H C ht ht1 hVQ →
      S.Lbar g ⊓ Nbar S g t ≠ zpowers t →
      (∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) →
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
        (∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) →
        ∀ w ∈ Wt S g t, ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

end CFSG.LargeExtraspecial.S9
