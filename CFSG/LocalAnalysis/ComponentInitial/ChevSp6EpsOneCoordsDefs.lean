module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Matrix

structure EpsOneVCoords {G : Type} [Group G] (Jh E₂ C₂ : Subgroup G) (z : G)
    (lev : GL (Fin 3) (ZMod 2) →* G) (δν : G → Fin 3 → ZMod 2)
    (cV : G → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Prop where
  mul : ∀ x ∈ Jh, ∀ y ∈ Jh, cV (x * y) = cV x + cV y
  eq_zero : ∀ x ∈ Jh, cV x = 0 ↔ x ∈ E₂
  surj : ∀ p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2), ∃ x ∈ Jh, cV x = p
  on_C₂ : ∀ c ∈ C₂, cV c = (δν c, 0)
  z_act : ∀ x ∈ Jh, cV (z * x * z⁻¹) = ((cV x).1 + (cV x).2, (cV x).2)
  lev_mem : ∀ g, lev g ∈ normalizer (Jh : Set G)
  lev_act : ∀ g, ∀ x ∈ Jh, cV (lev g * x * (lev g)⁻¹) =
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (cV x).1,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (cV x).2)

structure EpsOneECoords {G : Type} [Group G] (Jh E₂ : Subgroup G)
    (cV : G → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) (u : Bool)
    (cE : G → Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop where
  mul : ∀ e ∈ E₂, ∀ e' ∈ E₂, cE (e * e') = cE e + cE e'
  inj : ∀ e ∈ E₂, cE e = 0 → e = 1
  surj : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), ∃ e ∈ E₂, cE e = B
  sq : ∀ x ∈ Jh, cE (x * x) = vecMulVec (cV x).1 (cV x).1 + vecMulVec (cV x).1 (cV x).2 +
    if u then vecMulVec (cV x).2 (cV x).2 else 0

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
