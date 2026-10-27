module

public import CFSG.HardMathSupport.Kantor79.LongRoot
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K]
  {N : Type*} [AddCommGroup N] [Module K N] {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def axis (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (v : N) (c : K) :
    Submodule K V :=
  movedSpace (ρ (Tsp hBN v c))

@[expose] noncomputable def rootSpace (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (v : N) :
    Submodule K V :=
  ⨆ c : K, axis hBN ρ v c

structure Setting [Finite K] [CharP K 2] [FiniteDimensional K N] [FiniteDimensional K V]
    (hBN : BN.IsAlt) (Qf : QuadraticForm K V) (ρ : Gsp BN →* (V ≃ₗ[K] V)) : Prop where
  card : 4 ≤ Nat.card K
  nondegN : BN.Nondegenerate
  dimN : 4 ≤ finrank K N
  nondeg : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0
  iso : ∀ g v, Qf (ρ g v) = Qf v
  siegel : ∀ v : N, v ≠ 0 → ∀ c : K, c ≠ 0 → IsLongRootElement Qf (ρ (Tsp hBN v c))
  fix : ∀ v : V, (∀ g, ρ g v = v) → v = 0
  gen : commutatorSpace ρ.range = ⊤
  inj : Function.Injective ρ

@[expose] def CaseI (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) : Prop :=
  ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
    axis hBN ρ a 1 ⊓ axis hBN ρ c 1 ≠ ⊥

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
