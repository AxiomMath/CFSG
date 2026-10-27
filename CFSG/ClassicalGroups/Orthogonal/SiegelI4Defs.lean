module

public import CFSG.HardMathSupport.Kantor79.LongRoot
public import CFSG.ClassicalGroups.Alternating.I4SpDefs

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K]
  {N : Type*} [AddCommGroup N] [Module K N] {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V]

structure I4Setting [Finite K] [CharP K 2] [FiniteDimensional K N] [FiniteDimensional K V]
    (hBN : BN.IsAlt) (Qf : QuadraticForm K V) (ρ : Gsp BN →* (V ≃ₗ[K] V)) : Prop where
  card : 4 ≤ Nat.card K
  nondegN : BN.Nondegenerate
  dimN : 6 ≤ finrank K N
  nondeg : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0
  iso : ∀ g v, Qf (ρ g v) = Qf v
  siegel : ∀ a c : N, BN a c = 0 → LinearIndependent K ![a, c] →
    IsLongRootElement Qf (ρ (lineElt hBN a c))
  fix : ∀ v : V, (∀ g, ρ g v = v) → v = 0
  gen : commutatorSpace ρ.range = ⊤
  inj : Function.Injective ρ

@[expose] noncomputable def planeFamily (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    (π : Submodule K N) : Subgroup (V ≃ₗ[K] V) :=
  (planeGroup hBN π).map ρ

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
