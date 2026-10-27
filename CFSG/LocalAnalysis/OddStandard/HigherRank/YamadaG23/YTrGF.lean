module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

structure GFrame (Γ : Type) [Group Γ] where
  a₁ : Γ
  b₁ : Γ
  a₂ : Γ
  b₂ : Γ
  h₀ : Γ
  σ : Γ

namespace GFrame

variable {Γ : Type} [Group Γ] (gf : GFrame Γ)

@[expose] def z : Γ := gf.b₁ ^ 2

@[expose] def Z : Subgroup Γ := zpowers gf.z

@[expose] def S : Subgroup Γ := closure {gf.a₁, gf.b₁, gf.a₂, gf.b₂, gf.h₀}

@[expose] def A : Subgroup Γ := closure {gf.a₁, gf.b₁, gf.a₂, gf.b₂}

@[expose] def B : Subgroup Γ := centIn gf.S (closure {gf.b₁ * gf.b₂})

@[expose] def E : Subgroup Γ := closure {gf.b₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.a₂, gf.z}

@[expose] def F : Subgroup Γ := closure {gf.a₁ * gf.a₂, gf.b₁ * gf.b₂, gf.z}

@[expose] def Sσ : Subgroup Γ := closure {gf.a₁, gf.b₁, gf.a₂, gf.b₂, gf.h₀, gf.σ}

@[expose] def gens11 : Fin 6 → Γ := ![gf.a₁, gf.b₁, gf.a₂, gf.b₂, gf.h₀, gf.σ]

@[expose] def classes12 : Fin 7 → Set Γ := ![
  {gf.z},
  {gf.b₁ * gf.b₂, gf.b₁ * gf.b₂ * gf.z},
  {gf.a₁ * gf.a₂, gf.a₁ * gf.a₂ * gf.z, gf.a₁ * gf.b₁ * gf.a₂ * gf.b₂,
    gf.a₁ * gf.b₁ * gf.a₂ * gf.b₂ * gf.z},
  {gf.a₁ * gf.b₂, gf.a₁ * gf.b₂ * gf.z, gf.a₁ * gf.b₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.b₂ * gf.z},
  {gf.b₁ * gf.a₂, gf.b₁ * gf.a₂ * gf.z, gf.b₁ * gf.a₂ * gf.b₂, gf.b₁ * gf.a₂ * gf.b₂ * gf.z},
  {gf.a₁ * gf.b₁ * gf.a₂, gf.a₁ * gf.b₁ * gf.a₂ * gf.z, gf.a₁ * gf.a₂ * gf.b₂,
    gf.a₁ * gf.a₂ * gf.b₂ * gf.z},
  {gf.h₀, gf.h₀ * gf.z, gf.b₁ * gf.h₀, gf.b₁ * gf.h₀ * gf.z, gf.b₂ * gf.h₀,
    gf.b₂ * gf.h₀ * gf.z, gf.b₁ * gf.b₂ * gf.h₀, gf.b₁ * gf.b₂ * gf.h₀ * gf.z}]

@[expose] def reps13 : Fin 7 → Γ :=
  ![gf.z, gf.b₁ * gf.b₂, gf.a₁ * gf.a₂, gf.a₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.a₂, gf.h₀, gf.σ]

@[expose] def P11 : Prop :=
  ∃ h : ∀ r ∈ Frame.rels11, FreeGroup.lift gf.gens11 r = 1,
    Function.Injective (PresentedGroup.toGroup h) ∧ (PresentedGroup.toGroup h).range = gf.Sσ

variable [Finite Γ]

@[expose] def F12 : Prop :=
  {C : Set Γ | ∃ y ∈ invols gf.S, C = conjClass gf.S y} = Set.range gf.classes12 ∧
  Function.Injective gf.classes12 ∧
  centEl gf.S gf.z = gf.S ∧
  centEl gf.S (gf.b₁ * gf.b₂) = closure {gf.a₁ * gf.a₂, gf.b₁, gf.b₂, gf.h₀} ∧
  IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.a₂)) (gf.a₁ * gf.a₂) (closure {gf.a₁, gf.b₁ * gf.b₂}) ∧
  IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.b₂)) (gf.a₁ * gf.b₂) (closure {gf.a₁, gf.b₁ * gf.a₂}) ∧
  IsZ2xD8Decomp (centEl gf.S (gf.b₁ * gf.a₂)) (gf.b₁ * gf.a₂) (closure {gf.b₁, gf.a₁ * gf.b₂}) ∧
  IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂)) (gf.a₁ * gf.b₁ * gf.a₂)
    (closure {gf.a₂, gf.a₁ * gf.b₂}) ∧
  centEl gf.S gf.h₀ = closure {gf.b₁ * gf.b₂, gf.h₀, gf.z} ∧ IsE 3 ↥(centEl gf.S gf.h₀)

@[expose] def F13 : Prop :=
  centEl gf.S gf.σ = closure {gf.a₁ * gf.a₂, gf.b₁ * gf.b₂, gf.z} ∧
  {y : Γ | (∃ s ∈ gf.S, y = s * gf.σ) ∧ orderOf y = 2} =
    {y : Γ | ∃ c ∈ centEl gf.S gf.σ, y = c * gf.σ} ∧
  {y : Γ | ∃ c ∈ centEl gf.S gf.σ, y = c * gf.σ} = conjClass gf.S gf.σ ∧
  {C : Set Γ | ∃ y ∈ invols gf.Sσ, C = conjClass gf.Sσ y} =
    Set.range (fun i => conjClass gf.Sσ (gf.reps13 i)) ∧
  Function.Injective (fun i => conjClass gf.Sσ (gf.reps13 i)) ∧
  centEl gf.Sσ gf.z = gf.Sσ ∧
  centEl gf.Sσ (gf.b₁ * gf.b₂) = centEl gf.S (gf.b₁ * gf.b₂) ⊔ closure {gf.σ} ∧
  centEl gf.Sσ (gf.a₁ * gf.a₂) = centEl gf.S (gf.a₁ * gf.a₂) ⊔ closure {gf.σ} ∧
  centEl gf.Sσ (gf.a₁ * gf.b₂) = centEl gf.S (gf.a₁ * gf.b₂) ∧
  centEl gf.Sσ (gf.a₁ * gf.b₁ * gf.a₂) =
    centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂) ⊔ closure {gf.h₀ * gf.σ} ∧
  centEl gf.Sσ gf.h₀ = centEl gf.S gf.h₀ ⊔ closure {gf.b₁ * gf.σ} ∧
  centEl gf.Sσ gf.σ = centEl gf.S gf.σ ⊔ closure {gf.σ}

@[expose] def F14a : Prop :=
  (cen gf.S = gf.Z ∧ zSeries 2 gf.S = ⁅gf.S, gf.S⁆ ∧ ⁅gf.S, gf.S⁆ = closure {gf.b₁, gf.b₂} ∧
    SecProp gf.S (zSeries 2 gf.S) (fun Y _ _ _ => IsE 3 Y)) ∧
  (Nonempty (↥(closure {gf.a₁, gf.b₁} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    Nonempty (↥(closure {gf.a₂, gf.b₂} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    (∀ u ∈ (closure {gf.a₁, gf.b₁} : Subgroup Γ), ∀ v ∈ (closure {gf.a₂, gf.b₂} : Subgroup Γ),
      u * v = v * u) ∧
    closure {gf.a₁, gf.b₁} ⊔ closure {gf.a₂, gf.b₂} = gf.A ∧
    closure {gf.a₁, gf.b₁} ⊓ closure {gf.a₂, gf.b₂} = gf.Z ∧
    IsExtraspecialTwo 2 gf.A ∧ (∀ X : Subgroup Γ, X ≤ gf.S → IsExtraspecialTwo 2 X → X = gf.A))

@[expose] def F14b : Prop :=
  (cen gf.B = closure {gf.b₁ * gf.b₂, gf.z} ∧ cen gf.B = omega1 (zSeries 2 gf.S) ∧
    IsMaximalIn gf.S gf.B ∧ ¬ IsCyclic ↥(cen gf.B) ∧
    (∀ M : Subgroup Γ, IsMaximalIn gf.S M → ¬ IsCyclic ↥(cen M) → M = gf.B) ∧
    thompsonSubgroup gf.S = thompsonSubgroup gf.B ∧
    thompsonSubgroup gf.B = closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀} ∧
    Nonempty (↥(closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀} : Subgroup Γ) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    cen gf.B = omega1 (thompsonSubgroup gf.B) ∧
    ∀ y ∈ thompsonSubgroup gf.B, gf.h₀ * y * gf.h₀⁻¹ = y⁻¹)

@[expose] def F14c : Prop :=
  (gf.E ⊔ gf.F = gf.A ⊓ gf.B ∧
    IsZ2xD8Decomp (gf.A ⊓ gf.B) (gf.b₁ * gf.b₂) (closure {gf.a₁ * gf.a₂, gf.b₁}) ∧
    maxElemAbelian (gf.A ⊓ gf.B) = {gf.E, gf.F} ∧ gf.E ⊓ gf.F = cen gf.B) ∧
  (SecProp gf.S gf.F (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) =
        {(gf.A.subgroupOf gf.S).map π, (gf.B.subgroupOf gf.S).map π}) ∧
    SecProp gf.S gf.Z (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) = {(gf.A.subgroupOf gf.S).map π,
        ((zSeries 2 gf.S ⊔ closure {gf.h₀}).subgroupOf gf.S).map π}) ∧
    Nonempty (↥(zSeries 2 gf.S ⊔ closure {gf.h₀}) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) ∧
  ((maxElemAbelian gf.S).ncard = 8 ∧
    ∀ Y ∈ maxElemAbelian gf.S, ∃ s ∈ gf.S, ∃ Y₀ ∈ ({gf.E, gf.F, cen gf.B ⊔ closure {gf.h₀},
      closure {gf.a₁ * gf.b₂, gf.b₁ * gf.a₂, gf.z}, closure {gf.a₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.a₂,
        gf.z}} : Set (Subgroup Γ)), Y = conjSub s Y₀) ∧
  (pRank 2 gf.S = 3 ∧ GH74.sectionalTwoRank ↥gf.S = 4)

@[expose] def F14 : Prop := gf.F14a ∧ gf.F14b ∧ gf.F14c

@[expose] def F15a : Prop :=
  (cen gf.Sσ = gf.Z ∧ zSeries 2 gf.Sσ = cen gf.B ∧ zSeries 3 gf.Sσ = gf.E ⊔ gf.F ∧
    SecProp gf.Sσ (gf.E ⊔ gf.F) (fun Y _ _ _ => IsE 3 Y)) ∧
  (SecProp gf.Sσ (cen gf.B) (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) = {(gf.A.subgroupOf gf.Sσ).map π,
        ((gf.B ⊔ closure {gf.σ}).subgroupOf gf.Sσ).map π}) ∧
    SecProp (gf.B ⊔ closure {gf.σ}) gf.Z (fun Y _ _ _ => IsQ8StarQ8 Y)) ∧
  SecProp gf.Sσ gf.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = (gf.A.subgroupOf gf.Sσ).map π)

@[expose] def F15b : Prop :=
  (thompsonRank gf.Sσ = gf.F ⊔ closure {gf.σ} ∧ IsE 4 ↥(gf.F ⊔ closure {gf.σ}) ∧
    maxElemAbelian gf.Sσ = insert (gf.F ⊔ closure {gf.σ}) (maxElemAbelian gf.S) \ {gf.F}) ∧
  (∀ U : Subgroup Γ, U ≤ gf.Sσ → IsMulCommutative U → Nat.card U ≤ 16) ∧
  (pRank 2 gf.Sσ = 4 ∧ GH74.sectionalTwoRank ↥gf.Sσ = 4)

@[expose] def F15 : Prop := gf.F15a ∧ gf.F15b

end GFrame

@[expose] def GFrame.ofFrame {Γ : Type} [Group Γ] (fr : Frame Γ) : GFrame Γ :=
  ⟨fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ⟩

section Bridge

variable {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ)

theorem fact12_iff : fr.Fact12 ↔ (GFrame.ofFrame fr).F12 := Iff.rfl

theorem fact13_iff : fr.Fact13 ↔ (GFrame.ofFrame fr).F13 := Iff.rfl

theorem fact14_iff : fr.Fact14 ↔ (GFrame.ofFrame fr).F14 :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩

theorem fact15_iff : fr.Fact15 ↔ (GFrame.ofFrame fr).F15 :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩⟩

end Bridge

end CFSG.OddStandard.HigherRank.YamadaG23
