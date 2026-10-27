module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Conc
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplFinal
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4PartA
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4Setting

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem negT_producer (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hN : 4 ≤ finrank K N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (t₀ : Gsp BN) (ht₀ : t₀ * t₀ = 1) (ht₀1 : t₀ ≠ 1)
    (hsieg : finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0)
    (hT : finrank K (LinearMap.range
      (((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1)) ≠ 1)
    (hA2 : finrank K N = 4 → ∃ v : N,
      BN v ((((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1) v) ≠ 0)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0)
    (hV : commutatorSpace ρ.range = ⊤) :
    finrank K N = 6 ∧ finrank K V = 8 ∧
      ∀ U : AddSubgroup V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  obtain ⟨h6, a₀, c₀, hac₀, hli₀, rfl⟩ :=
    six_le_finrank_and_exists_lineElt hq hBN hBNnd hN Qf hnd ρ hρQ t₀ ht₀ ht₀1 hsieg hT hA2
  have hs := i4Setting_of hq hBN hBNnd h6 Qf hnd ρ hρQ hac₀ hli₀ hsieg hC hV
  exact conc_all_conclusion hs ((conc_all_or_copl_all hs).resolve_right (not_copl_all hs))

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
