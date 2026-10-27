module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure S8Data {P : Type} [Group P] (V1 V2 : Subgroup P) (φ1 φ2 : (Fin 5 → ZMod 2) → P)
    (α β : P →* S8A5) : Prop where
  coord1 : Sec128Coord V1 φ1
  coord2 : Sec128Coord V2 φ2
  comm : ∀ x ∈ V1, ∀ y ∈ V2, x * y = y * x
  disj : V1 ⊓ V2 = ⊥
  act1 : ∀ (g : P) (v : Fin 5 → ZMod 2), IsEvenVec v →
    g * φ1 v * g⁻¹ = φ1 (permVec ((α g : S8A5) : Equiv.Perm (Fin 5)) v)
  act2 : ∀ (g : P) (v : Fin 5 → ZMod 2), IsEvenVec v →
    g * φ2 v * g⁻¹ = φ2 (permVec ((β g : S8A5) : Equiv.Perm (Fin 5)) v)
  ker : ∀ g : P, α g = 1 → β g = 1 → g ∈ V1 ⊔ V2
  surj : ∀ a b : S8A5, ∃ g : P, α g = a ∧ β g = b

@[expose] def s8H {P : Type} [Group P] (V : Subgroup P) : Subgroup P :=
  ⁅centralizer (V : Set P), centralizer (V : Set P)⁆

end CFSG.OddStandard.SmallF3.Omega
