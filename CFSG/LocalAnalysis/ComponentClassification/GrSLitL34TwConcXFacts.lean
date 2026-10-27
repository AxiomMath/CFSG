module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def cosT (i : Bool) : Set (Equiv.Perm (Fin 42)) :=
  if i then {y | ∃ x ∈ T0, y = x * r₄} else (T0 : Set (Equiv.Perm (Fin 42)))

@[expose] def cosC (i : Bool) (t u : Equiv.Perm (Fin 42)) : Set (Equiv.Perm (Fin 42)) :=
  {y | y ∈ cosT i ∧ y * t = t * y ∧ y * u = u * y}

@[expose] def cosC₂ (i : Bool) (t u : Equiv.Perm (Fin 42)) : Set (Equiv.Perm (Fin 42)) :=
  {y | y ∈ cosC i t u ∧ y * y = 1}

structure ConcXFacts : Prop where
  cent : ∃ z ∈ T0, z * z = 1 ∧ z ≠ 1 ∧ z * g₅ = g₅ * z ∧ z * g₆ = g₆ * z ∧
    ∀ x ∈ T0, z * x = x * z
  inv : ∃ x ∈ T0, x * r₄ * (x * r₄) = 1
  uni : ∀ x ∈ T0, x * r₄ * (x * r₄) = 1 → ∃ c ∈ T0, x * r₄ * c = c * r₄
  big : ∀ t ∈ T0, t * t = 1 → 16 ≤ Nat.card (cosC false t t)
  qcard : ∀ v ∈ cosT true, v * v = 1 → ∀ i, Nat.card (cosC i v v) ≤ 8
  qinv : ∀ v ∈ cosT true, v * v = 1 → ∀ i, Nat.card (cosC₂ i v v) ≤ 2
  qsq : ∀ v ∈ cosT true, v * v = 1 → ∀ i, ∀ y ∈ cosC i v v, y * y * (y * y) = 1
  pcard : ∀ t ∈ T0, t * t = 1 → t ≠ 1 → ∀ u ∈ cosT true, u * u = 1 → t * u = u * t →
    Nat.card (cosC false t u) * 8 + Nat.card (cosC true t u) * 8 ≤ 128
  pinv : ∀ t ∈ T0, t * t = 1 → t ≠ 1 → ∀ u ∈ cosT true, u * u = 1 → t * u = u * t →
    Nat.card (cosC₂ false t u) * 2 + Nat.card (cosC₂ true t u) * 2 < 16
  psq : ∀ t ∈ T0, t * t = 1 → t ≠ 1 → ∀ u ∈ cosT true, u * u = 1 → t * u = u * t →
    ∀ i, ∀ y ∈ cosC i t u, y * y = 1 ∨ y * y = t

end CFSG.ComponentClassification.GrSLit.L34Tw

end
