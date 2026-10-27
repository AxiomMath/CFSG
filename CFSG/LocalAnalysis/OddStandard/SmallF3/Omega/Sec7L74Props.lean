module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec74Ass (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) :
    Prop where
  ctx : Sec7Ctx G t L S z
  comm : g⁻¹ * t * g ∈ centralizer ({t} : Set G)
  ne : g⁻¹ * t * g ≠ t
  not1 : ¬ IsConj t (t * z)

@[expose] def Sec74NotI4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G),
    Sec74Ass G t L S z g → ¬ InducesTypeSome L (g⁻¹ * t * g) 6 1 4 1

@[expose] def Sec74CaseC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G),
    Sec74Ass G t L S z g →
      ((∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 (g⁻¹ * t * g)) → False

@[expose] def Sec74BX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G),
    Sec74Ass G t L S z g → InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1) →
      IsL29 (layerCent L (g⁻¹ * t * g)) ∧ layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g ∧
        ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
          InducesTypeSome L u 6 1 2 (-1) ∧ InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1)

@[expose] def Sec74BT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G),
    Sec74Ass G t L S z g → InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1) →
      InducesTypeSome (CFSG.conjugate L g) t 6 1 2 (-1) ∧
        layerCent (CFSG.conjugate L g) t = layerCent L (g⁻¹ * t * g)

@[expose] def Sec74CaseB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G),
    Sec74Ass G t L S z g → InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1) → False

end CFSG.OddStandard.SmallF3.Omega
