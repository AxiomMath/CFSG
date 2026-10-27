module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperGen
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.HyperQuotient

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

structure IsUnitaryCover {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) {G : Type} [Group G]
    (π : SUid σ n →* G) : Prop where
  involution : IsUnitaryInvolution σ
  two_le : 2 ≤ n
  exists_norm : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1
  surjective : Function.Surjective π
  ker_scalar : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1

@[expose] def UReducible (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K) (π : SUid σ n →* Cat d),
    IsUnitaryCover σ π ∧ (p : K) ≠ 0 ∧
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      ∀ g : SUid σ n, π g ∈ E₀ → ∀ w ∈ W, g • w ∈ W

theorem seitzHyperLie_unitaryReducible : SeitzHyperLie fun d p E₀ => UReducible d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hred
  obtain ⟨n, K, _, _, σ, π, hc, hpK, W, hW0, hWiso, hWstab⟩ := hred
  exact hyperGen_top_of_isotropic_unitary hc.involution hc.two_le hc.exists_norm π hc.surjective
    hc.ker_scalar hp hp2 hpK hE hcard hW0 hWiso hWstab

end CFSG.LieType.SeitzGeneration
