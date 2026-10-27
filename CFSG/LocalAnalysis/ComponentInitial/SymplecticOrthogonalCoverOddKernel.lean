module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryCoverOddKernel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCatalogCover
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverCatalog
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverPrime
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFive
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalogCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Assembly.LowTwoRank

theorem even_symplectic_orthogonal_perfect_central_kernel_odd_off_two_boundaries {E : Type*}
    {T : Type} [Group E] [Group T] [Finite E] [Finite T] [Group.IsPerfect E] (η : E →* T)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) {τ : StatedLieTag}
    (hτ : τ = .PSp ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) {n f : ℕ}
    (hT : StatedClassicalModel T τ n 2 f)
    (hoff : (τ, n, f) ∉ [(.PSp, 3, 1), (.POmegaPlus, 4, 1)]) :
    Odd (Nat.card η.ker) := by
  have hL : CFSG.Blueprint.LieModel T τ n 2 f :=
    Or.inl ⟨by rcases hτ with rfl | rfl | rfl <;> decide, hT⟩
  refine odd_card_ker_of_two_cover_trivial η hη hC fun θ hθ hθC h2 => ?_
  obtain ⟨-, hf, hadm⟩ := hT.1
  rcases hτ with rfl | rfl | rfl
  ·
    obtain ⟨hn, hne⟩ := hadm
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    ·
      have hn4 : 4 ≤ n := by
        by_contra h
        interval_cases n
        · exact hne rfl
        · exact hoff (by simp)
      exact (SymplecticCoverHigher.even_higher_symplectic_prime_field_central_two_cover_trivial
        θ hθ hθC h2 hn4 hL).1
    · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · exact (SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
          θ hθ hθC h2 hf2 hL).1
      · exact (even_higher_symplectic_catalog_perfect_central_two_cover_trivial θ hθ hθC h2 hn3
          hf2 hL).1
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    ·
      have hn5 : 5 ≤ n := by
        by_contra h
        obtain rfl : n = 4 := by omega
        exact hoff (by simp)
      exact (even_split_orthogonal_prime_field_central_two_cover_trivial θ hθ hθC h2 hn5 hL).1
    · exact (even_split_orthogonal_catalog_perfect_central_two_cover_trivial θ hθ hθC h2 hadm hf2
        hL).1
  ·
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
    · rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | hn6
      · exact (even_nonsplit_orthogonal_four_prime_field_central_two_cover_trivial θ hθ hθC h2
          hL).1
      · exact (even_nonsplit_orthogonal_five_prime_field_central_two_cover_trivial θ hθ hθC h2
          hL).1
      · exact (even_higher_nonsplit_orthogonal_prime_field_central_two_cover_trivial θ hθ hθC h2
          hn6 hL).1
    · exact (even_nonsplit_orthogonal_catalog_perfect_central_two_cover_trivial θ hθ hθC h2 hadm
        hf2 hL).1

end CFSG.LocalAnalysis.ComponentInitial
