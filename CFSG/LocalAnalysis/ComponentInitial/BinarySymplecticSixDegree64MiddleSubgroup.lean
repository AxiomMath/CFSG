module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Intersection

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

omit hinf in
include hzC hz in
theorem leviHom_mem_normalizer_of [Finite G] {D₂ : Subgroup G}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (g : GL (Fin 3) (ZMod 2)) :
    leviHom φ he g ∈ normalizer (D₂ : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨d, hd, rfl⟩
  exact hD₂n _ (leviHom_mem_normalizer_radSub φ he hzC hz g) d hd

@[expose] def leviAct [Finite G] {D₂ : Subgroup G}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) : GL (Fin 3) (ZMod 2) →* MulAut D₂ :=
  (conjNormalizer D₂).comp ((leviHom φ he).codRestrict (normalizer (D₂ : Set G))
    (leviHom_mem_normalizer_of he φ hzC hz hD₂n))

omit hinf in
theorem coe_leviAct [Finite G] {D₂ : Subgroup G}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (g : GL (Fin 3) (ZMod 2)) (d : D₂) :
    ((leviAct he φ hzC hz hD₂n g d : D₂) : G) = leviHom φ he g * d * (leviHom φ he g)⁻¹ :=
  rfl

theorem symThreeAffine_eq (κ : ZMod 2) (C B : ↥(binarySymMatrices 3)) :
    B + κ • symThreePolarSym (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + (1 : ZMod 2) • C =
      symThreeAffine κ C B :=
  Subtype.ext (by
    change (B : M₃) + κ • symThreePolar (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) +
      (1 : ZMod 2) • (C : M₃) = (B : M₃) + C + κ • symThreePolar (symThreeDiag C) (symThreeDiag B)
    rw [one_smul, add_right_comm])

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
