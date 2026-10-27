module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem commutator_le_of_index_le_two {A : Type*} [Group A] [Finite A] {N : Subgroup A}
    [N.Normal] (h : N.index ≤ 2) : commutator A ≤ N := by
  have hpos : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 by omega) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (A ⧸ N) := isCyclic_of_prime_card h2
    infer_instance

theorem finite_mulAut (K : Type) [Field K] [Finite K] :
    Finite (MulAut (StatedProj (StatedSp 2 K))) :=
  Finite.of_injective (fun σ : MulAut (StatedProj (StatedSp 2 K)) =>
    (σ : StatedProj (StatedSp 2 K) → StatedProj (StatedSp 2 K))) DFunLike.coe_injective

theorem symplectic_two_schreier (K : Type) [Field K] [Finite K] :
    derivedSeries (Outer (StatedProj (StatedSp 2 K))) 3 = ⊥ ∧
      Group.IsSolvable (Outer (StatedProj (StatedSp 2 K))) := by
  have := finite_mulAut K
  obtain ⟨-, -, hEn, hEi⟩ := kernel_generation (K := K)
  have h2 := (standard_outer_quotient (K := K) (r := 2) (by omega)).2.2.2.2.2
  have h1 : derivedSeries (MulAut (StatedProj (StatedSp 2 K))) 1 ≤ spSemilinearAutGroup 2 K := by
    rw [derivedSeries_one]
    exact commutator_le_of_index_le_two hEi
  have h3 : derivedSeries (MulAut (StatedProj (StatedSp 2 K))) 3 ≤
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
    have h2' : derivedSeries (MulAut (StatedProj (StatedSp 2 K))) 2 ≤
        ⁅spSemilinearAutGroup 2 K, spSemilinearAutGroup 2 K⁆ := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mono h1 h1
    rw [derivedSeries_succ]
    exact (Subgroup.commutator_mono h2' h2').trans h2
  have hder : derivedSeries (Outer (StatedProj (StatedSp 2 K))) 3 = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (inner _)), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact h3
  exact ⟨hder, ⟨⟨3, hder⟩⟩⟩

theorem classical_model_two_schreier {G : Type} [Group G] {p f : ℕ}
    (h : StatedClassicalModel G .PSp 2 p f) :
    derivedSeries (Outer G) 3 = ⊥ ∧ Group.IsSolvable (Outer G) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  obtain ⟨hder, hsolv⟩ := symplectic_two_schreier K
  obtain ⟨⟨e', -⟩, hiff⟩ := outer_isomorphism e
  refine ⟨?_, hiff.mpr hsolv⟩
  rw [← map_derivedSeries_eq (f := e'.symm.toMonoidHom) e'.symm.surjective, hder,
    Subgroup.map_bot]

theorem classical_model_two_schreier_of_classicalModel {G : Type} [Group G] {p f : ℕ}
    [Fact p.Prime] (h : Assembly.ComponentType.ClassicalModel G .PSp 2 p f) :
    derivedSeries (Outer G) 3 = ⊥ ∧ Group.IsSolvable (Outer G) :=
  classical_model_two_schreier
    (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSp 2 p f h)

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
