module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem ker_comp_mulEquiv {E Q X : Type*} [Group E] [Group Q] [Group X] (η : E →* Q)
    (e : Q ≃* X) : (e.toMonoidHom.comp η).ker = η.ker := by
  ext x
  exact e.map_eq_one_iff

theorem even_linear_unitary_rank_one_catalog_central_two_cover_trivial {E : Type*} {Q : Type}
    [Group E] [Group Q] [Finite E] [Group.IsPerfect E] (η : E →* Q)
    (hη : Function.Surjective η) (h2 : IsPGroup 2 η.ker) (hC : η.ker ≤ center E)
    (hQ : (∃ f : ℕ, 3 ≤ f ∧ CFSG.Blueprint.LieModel Q .PSL 2 2 f) ∨
      ∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel Q .PSU 3 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  suffices hker : η.ker = ⊥ from ⟨hker, (MonoidHom.ker_eq_bot_iff η).1 hker, hη⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hQ with ⟨f, hf, hL⟩ | ⟨f, hf, hU⟩
  · obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
    let : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    let e' := e.trans (LinearCover.projectiveSLTwoEquivSL K)
    have hk := ker_comp_mulEquiv η e'
    rw [← hk]
    exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot f hf
      hcard (e'.toMonoidHom.comp η) (e'.surjective.comp hη) (by rw [hk]; exact hC)
      (by rw [hk]; exact h2)
  · rcases hU with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hc
      have hcard' : Nat.card K = 2 ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
      let : Fintype K := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
      let e' : Q ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
      have hk := ker_comp_mulEquiv η e'
      rw [← hk]
      exact (CFSG.ShultStronglyClosedTI.even_unitary_three_perfect_central_two_cover_trivial f
        hf hcard' (e'.toMonoidHom.comp η) (e'.surjective.comp hη) (by rw [hk]; exact hC)
        (by rw [hk]; exact h2)).1
    all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
