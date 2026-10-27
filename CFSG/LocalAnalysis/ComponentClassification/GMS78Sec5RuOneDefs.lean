module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Facts
public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Sec3.SzR.SteinbergCoords (L T R : Subgroup G) : Prop :=
  ∃ (e : gmsA L T ≃* Multiplicative (Fin 3 → ZMod 2))
    (χ : R →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))),
    χ.ker = (gmsA L T).subgroupOf R ∧
    (∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s))) ∧
    (∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
    ∀ g ∈ normalizer (R : Set G), ∀ P : SL(3, ZMod 2),
      (∀ a b : gmsA L T, (b : G) = g * a * g⁻¹ →
        e b = Multiplicative.ofAdd ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
          (Multiplicative.toAdd (e a)))) →
      ∀ s t : R, (t : G) = g * s * g⁻¹ →
        χ t = Multiplicative.ofAdd (RuType.stAct P (Multiplicative.toAdd (χ s)))

end CFSG.ComponentClassification.GMS78
