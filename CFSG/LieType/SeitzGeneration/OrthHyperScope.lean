module

public import CFSG.LieType.SeitzGeneration.OrthHyperGen
public import CFSG.LieType.SeitzGeneration.OrthHyperModel
public import CFSG.LieType.SeitzGeneration.HyperQuotient
public import CFSG.RankThree.PartOne.CTP.SeitzOrthKernel

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.RankThree.PartOne.CTP

@[expose] def OReducible (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (K V : Type) (_ : Field K) (_ : Finite K) (_ : AddCommGroup V) (_ : Module K V)
    (_ : FiniteDimensional K V) (Q : QuadraticForm K V) (π : elementaryGroup Q →* Cat d),
    IsOrthogonalCover Q π ∧ (p : K) ≠ 0 ∧
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ g : elementaryGroup Q, π g ∈ E₀ → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W

theorem not_dvd_card_ker_of_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} [Nontrivial V] [Finite K] [FiniteDimensional K V]
    {G : Type} [Group G] {π : elementaryGroup Q →* G} (hc : IsOrthogonalCover Q π) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card π.ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hfinV : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) p hdvd
  have hsq : (z : elementaryGroup Q) ^ 2 = 1 := by
    apply Subtype.ext
    exact sq_eq_one_of_mem_scalars hc.nondegenerate
      (elementaryGroup_le_orthogonalGroup Q (z : elementaryGroup Q).2) (hc.ker_scalar z z.2)
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hsq)
  rw [hz] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem seitzHyperLie_orthReducible : SeitzHyperLie fun d p E₀ => OReducible d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hred
  obtain ⟨K, V, _, _, _, _, _, Q, π, hc, hpK, W, hW0, hWQ, hWstab⟩ := hred
  obtain ⟨w, -, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩
  exact hyperGen_top_of_singular_stable hc.nondegenerate rfl π hc.surjective hp hp2 hpK
    (not_dvd_card_ker_of_scalar hc hp hp2) hE hcard hW0 hWQ hWstab

end CFSG.LieType.SeitzGeneration
