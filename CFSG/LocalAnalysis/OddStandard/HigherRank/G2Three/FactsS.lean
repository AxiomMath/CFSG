module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1

open Subgroup CFSG.Open
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ)

namespace Frame

@[expose] def rels11 : Set (FreeGroup (Fin 6)) :=
  let a₁ : FreeGroup (Fin 6) := FreeGroup.of 0
  let b₁ : FreeGroup (Fin 6) := FreeGroup.of 1
  let a₂ : FreeGroup (Fin 6) := FreeGroup.of 2
  let b₂ : FreeGroup (Fin 6) := FreeGroup.of 3
  let h₀ : FreeGroup (Fin 6) := FreeGroup.of 4
  let σ : FreeGroup (Fin 6) := FreeGroup.of 5
  let z : FreeGroup (Fin 6) := b₁ ^ 2
  {r | r ∈ [z ^ 2, h₀ ^ 2, σ ^ 2, a₁ ^ 2 * z⁻¹, a₂ ^ 2 * z⁻¹, b₂ ^ 2 * z⁻¹,
    ⁅a₁, b₁⁆ * z⁻¹, ⁅a₂, b₂⁆ * z⁻¹,
    ⁅a₁, h₀⁆ * (b₁ * z)⁻¹, ⁅a₂, h₀⁆ * (b₂ * z)⁻¹, ⁅b₁, h₀⁆ * z⁻¹, ⁅b₂, h₀⁆ * z⁻¹,
    ⁅a₁, σ⁆ * (a₁ * a₂ * z)⁻¹, ⁅a₂, σ⁆ * (a₁ * a₂ * z)⁻¹,
    ⁅b₁, σ⁆ * (b₁ * b₂ * z)⁻¹, ⁅b₂, σ⁆ * (b₁ * b₂ * z)⁻¹, ⁅h₀, σ⁆ * z⁻¹,
    ⁅a₁, a₂⁆, ⁅a₁, b₂⁆, ⁅b₁, a₂⁆, ⁅b₁, b₂⁆]}

@[expose] def gens11 : Fin 6 → Γ := ![fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ]

@[expose] def Fact11 (L : Subgroup Γ) : Prop :=
  (∃ h : ∀ r ∈ rels11, FreeGroup.lift fr.gens11 r = 1,
    Function.Injective (PresentedGroup.toGroup h) ∧ (PresentedGroup.toGroup h).range = fr.Sσ) ∧
  IsSylowIn 2 L fr.S ∧ IsSylowIn 2 ⊤ fr.Sσ

@[expose] def classes12 : Fin 7 → Set Γ := ![
  {fr.z},
  {fr.b₁ * fr.b₂, fr.b₁ * fr.b₂ * fr.z},
  {fr.a₁ * fr.a₂, fr.a₁ * fr.a₂ * fr.z, fr.a₁ * fr.b₁ * fr.a₂ * fr.b₂,
    fr.a₁ * fr.b₁ * fr.a₂ * fr.b₂ * fr.z},
  {fr.a₁ * fr.b₂, fr.a₁ * fr.b₂ * fr.z, fr.a₁ * fr.b₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.b₂ * fr.z},
  {fr.b₁ * fr.a₂, fr.b₁ * fr.a₂ * fr.z, fr.b₁ * fr.a₂ * fr.b₂, fr.b₁ * fr.a₂ * fr.b₂ * fr.z},
  {fr.a₁ * fr.b₁ * fr.a₂, fr.a₁ * fr.b₁ * fr.a₂ * fr.z, fr.a₁ * fr.a₂ * fr.b₂,
    fr.a₁ * fr.a₂ * fr.b₂ * fr.z},
  {fr.h₀, fr.h₀ * fr.z, fr.b₁ * fr.h₀, fr.b₁ * fr.h₀ * fr.z, fr.b₂ * fr.h₀,
    fr.b₂ * fr.h₀ * fr.z, fr.b₁ * fr.b₂ * fr.h₀, fr.b₁ * fr.b₂ * fr.h₀ * fr.z}]

@[expose] def Fact12 : Prop :=
  {C : Set Γ | ∃ y ∈ invols fr.S, C = conjClass fr.S y} = Set.range fr.classes12 ∧
  Function.Injective fr.classes12 ∧
  centEl fr.S fr.z = fr.S ∧
  centEl fr.S (fr.b₁ * fr.b₂) = closure {fr.a₁ * fr.a₂, fr.b₁, fr.b₂, fr.h₀} ∧
  IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.a₂)) (fr.a₁ * fr.a₂) (closure {fr.a₁, fr.b₁ * fr.b₂}) ∧
  IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.b₂)) (fr.a₁ * fr.b₂) (closure {fr.a₁, fr.b₁ * fr.a₂}) ∧
  IsZ2xD8Decomp (centEl fr.S (fr.b₁ * fr.a₂)) (fr.b₁ * fr.a₂) (closure {fr.b₁, fr.a₁ * fr.b₂}) ∧
  IsZ2xD8Decomp (centEl fr.S (fr.a₁ * fr.b₁ * fr.a₂)) (fr.a₁ * fr.b₁ * fr.a₂)
    (closure {fr.a₂, fr.a₁ * fr.b₂}) ∧
  centEl fr.S fr.h₀ = closure {fr.b₁ * fr.b₂, fr.h₀, fr.z} ∧ IsE 3 ↥(centEl fr.S fr.h₀)

@[expose] def reps13 : Fin 7 → Γ :=
  ![fr.z, fr.b₁ * fr.b₂, fr.a₁ * fr.a₂, fr.a₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂, fr.h₀, fr.σ]

@[expose] def Fact13 : Prop :=
  centEl fr.S fr.σ = closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z} ∧
  {y : Γ | (∃ s ∈ fr.S, y = s * fr.σ) ∧ orderOf y = 2} =
    {y : Γ | ∃ c ∈ centEl fr.S fr.σ, y = c * fr.σ} ∧
  {y : Γ | ∃ c ∈ centEl fr.S fr.σ, y = c * fr.σ} = conjClass fr.S fr.σ ∧
  {C : Set Γ | ∃ y ∈ invols fr.Sσ, C = conjClass fr.Sσ y} =
    Set.range (fun i => conjClass fr.Sσ (fr.reps13 i)) ∧
  Function.Injective (fun i => conjClass fr.Sσ (fr.reps13 i)) ∧
  centEl fr.Sσ fr.z = fr.Sσ ∧
  centEl fr.Sσ (fr.b₁ * fr.b₂) = centEl fr.S (fr.b₁ * fr.b₂) ⊔ closure {fr.σ} ∧
  centEl fr.Sσ (fr.a₁ * fr.a₂) = centEl fr.S (fr.a₁ * fr.a₂) ⊔ closure {fr.σ} ∧
  centEl fr.Sσ (fr.a₁ * fr.b₂) = centEl fr.S (fr.a₁ * fr.b₂) ∧
  centEl fr.Sσ (fr.a₁ * fr.b₁ * fr.a₂) =
    centEl fr.S (fr.a₁ * fr.b₁ * fr.a₂) ⊔ closure {fr.h₀ * fr.σ} ∧
  centEl fr.Sσ fr.h₀ = centEl fr.S fr.h₀ ⊔ closure {fr.b₁ * fr.σ} ∧
  centEl fr.Sσ fr.σ = centEl fr.S fr.σ ⊔ closure {fr.σ}

@[expose] def Fact14 : Prop :=
  (cen fr.S = fr.Z ∧ zSeries 2 fr.S = ⁅fr.S, fr.S⁆ ∧ ⁅fr.S, fr.S⁆ = closure {fr.b₁, fr.b₂} ∧
    SecProp fr.S (zSeries 2 fr.S) (fun Y _ _ _ => IsE 3 Y)) ∧
  (Nonempty (↥(closure {fr.a₁, fr.b₁} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    Nonempty (↥(closure {fr.a₂, fr.b₂} : Subgroup Γ) ≃* QuaternionGroup 2) ∧
    (∀ u ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ), ∀ v ∈ (closure {fr.a₂, fr.b₂} : Subgroup Γ),
      u * v = v * u) ∧
    closure {fr.a₁, fr.b₁} ⊔ closure {fr.a₂, fr.b₂} = fr.A ∧
    closure {fr.a₁, fr.b₁} ⊓ closure {fr.a₂, fr.b₂} = fr.Z ∧
    IsExtraspecialTwo 2 fr.A ∧ (∀ X : Subgroup Γ, X ≤ fr.S → IsExtraspecialTwo 2 X → X = fr.A)) ∧
  (cen fr.B = closure {fr.b₁ * fr.b₂, fr.z} ∧ cen fr.B = omega1 (zSeries 2 fr.S) ∧
    IsMaximalIn fr.S fr.B ∧ ¬ IsCyclic ↥(cen fr.B) ∧
    (∀ M : Subgroup Γ, IsMaximalIn fr.S M → ¬ IsCyclic ↥(cen M) → M = fr.B) ∧
    thompsonSubgroup fr.S = thompsonSubgroup fr.B ∧
    thompsonSubgroup fr.B = closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} ∧
    Nonempty (↥(closure {fr.b₁, fr.a₁ * fr.a₂ * fr.h₀} : Subgroup Γ) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    cen fr.B = omega1 (thompsonSubgroup fr.B) ∧
    ∀ y ∈ thompsonSubgroup fr.B, fr.h₀ * y * fr.h₀⁻¹ = y⁻¹) ∧
  (fr.E ⊔ fr.F = fr.A ⊓ fr.B ∧
    IsZ2xD8Decomp (fr.A ⊓ fr.B) (fr.b₁ * fr.b₂) (closure {fr.a₁ * fr.a₂, fr.b₁}) ∧
    maxElemAbelian (fr.A ⊓ fr.B) = {fr.E, fr.F} ∧ fr.E ⊓ fr.F = cen fr.B) ∧
  (SecProp fr.S fr.F (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) =
        {(fr.A.subgroupOf fr.S).map π, (fr.B.subgroupOf fr.S).map π}) ∧
    SecProp fr.S fr.Z (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) = {(fr.A.subgroupOf fr.S).map π,
        ((zSeries 2 fr.S ⊔ closure {fr.h₀}).subgroupOf fr.S).map π}) ∧
    Nonempty (↥(zSeries 2 fr.S ⊔ closure {fr.h₀}) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) ∧
  ((maxElemAbelian fr.S).ncard = 8 ∧
    ∀ Y ∈ maxElemAbelian fr.S, ∃ s ∈ fr.S, ∃ Y₀ ∈ ({fr.E, fr.F, cen fr.B ⊔ closure {fr.h₀},
      closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}, closure {fr.a₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂,
        fr.z}} : Set (Subgroup Γ)), Y = conjSub s Y₀) ∧
  (pRank 2 fr.S = 3 ∧ GH74.sectionalTwoRank ↥fr.S = 4)

@[expose] def Fact15 : Prop :=
  (cen fr.Sσ = fr.Z ∧ zSeries 2 fr.Sσ = cen fr.B ∧ zSeries 3 fr.Sσ = fr.E ⊔ fr.F ∧
    SecProp fr.Sσ (fr.E ⊔ fr.F) (fun Y _ _ _ => IsE 3 Y)) ∧
  (SecProp fr.Sσ (cen fr.B) (fun Y _ _ π =>
      maxElemAbelian (⊤ : Subgroup Y) = {(fr.A.subgroupOf fr.Sσ).map π,
        ((fr.B ⊔ closure {fr.σ}).subgroupOf fr.Sσ).map π}) ∧
    SecProp (fr.B ⊔ closure {fr.σ}) fr.Z (fun Y _ _ _ => IsQ8StarQ8 Y)) ∧
  SecProp fr.Sσ fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = (fr.A.subgroupOf fr.Sσ).map π) ∧
  (thompsonRank fr.Sσ = fr.F ⊔ closure {fr.σ} ∧ IsE 4 ↥(fr.F ⊔ closure {fr.σ}) ∧
    maxElemAbelian fr.Sσ = insert (fr.F ⊔ closure {fr.σ}) (maxElemAbelian fr.S) \ {fr.F}) ∧
  (∀ U : Subgroup Γ, U ≤ fr.Sσ → IsMulCommutative U → Nat.card U ≤ 16) ∧
  (pRank 2 fr.Sσ = 4 ∧ GH74.sectionalTwoRank ↥fr.Sσ = 4)

end Frame

end CFSG.OddStandard.HigherRank.G2Three.Sec1
