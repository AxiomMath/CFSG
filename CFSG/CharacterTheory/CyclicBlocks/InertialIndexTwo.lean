module

public import CFSG.CharacterTheory.CyclicBlocks.AbelianInertialIndexTwo

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

theorem exists_eq_zpowers_of_isCyclic {G : Type*} [Group G] (H : Subgroup G) [IsCyclic H] :
    ∃ u : G, H = Subgroup.zpowers u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.zpow_mem _ g.2 k

theorem principal_block_cyclic_sylow_inertial_index_two {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (P : Sylow p G) (hcyc : IsCyclic (P : Subgroup G))
    (hN : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (ψ₁ : basis.index) (ψ : ℕ → basis.index) (δ : ℤ),
      (δ = 1 ∨ δ = -1) ∧ ψ₁ ≠ principal ∧
      Set.InjOn ψ (Finset.Icc 1 ((Nat.card P - 1) / 2)) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2), ψ μ ≠ principal ∧ ψ μ ≠ ψ₁) ∧
      (∀ g : G, p ∣ orderOf g → (basis.representation ψ₁).character g = δ) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2),
        (Module.finrank ℂ (basis.representation (ψ μ)).vector : ℤ) =
          Module.finrank ℂ (basis.representation ψ₁).vector + δ) ∧
      (∀ g : G, starRingEnd ℂ ((basis.representation ψ₁).character g) =
        (basis.representation ψ₁).character g) ∧
      (∀ μ ∈ Finset.Icc 1 ((Nat.card P - 1) / 2), ∀ g : G,
        starRingEnd ℂ ((basis.representation (ψ μ)).character g) =
          (basis.representation (ψ μ)).character g) ∧
      (Nat.card P = 3 → ∀ g : G, p ∣ orderOf g →
        (basis.representation (ψ 1)).character g = -δ) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨u, hPu⟩ := exists_eq_zpowers_of_isCyclic (P : Subgroup G)
  have hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2 := by
    rw [← hPu]
    exact hN
  obtain ⟨τ, hτN, -, hτ⟩ := exists_mem_normalizer_conj_eq_inv_of_dvd_prime_pow hpp hp
    (orderOf_dvd_of_sylow_eq_zpowers P hPu) hindex
  refine principal_block_abelian_sylow_inverting_index_two basis ideal p hp principal hprincipal P
    (fun x hx y hy => ?_) hN τ (by rw [← hPu] at hτN; exact hτN) (fun x hx => ?_)
  · rw [hPu] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_add, ← zpow_add, add_comm]
  · rw [hPu] at hx
    exact conj_mem_zpowers_eq_inv hx hτ

end CFSG.CyclicBlocks
