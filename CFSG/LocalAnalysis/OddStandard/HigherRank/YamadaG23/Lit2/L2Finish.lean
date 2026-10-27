module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Sylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem l2_pauli_finish {G S : Type} [Group G] [Group S] [Finite S] (π : G →* S)
    (hπs : Function.Surjective π) {A : Subgroup S} {m : G} (hm1 : m ≠ 1)
    (hcen : ∀ u ∈ π.ker, ∀ x : G, u * x = x * u)
    (hP2 : ∀ x : G, π x ∈ A → π x ≠ 1 → ∃ y : G, π y ∈ A ∧ ⁅x, y⁆ = m)
    {a₁ b₁ a₂ b₂ : G}
    (hgen : ∀ y : G, π y ∈ A →
      y ∈ Subgroup.closure (({a₁, b₁, a₂, b₂} : Set G) ∪ (π.ker : Set G)))
    {g : G} (hg2 : g * g = 1) (hgn : g ∉ π.ker)
    (h₁ : g * a₁ = a₁ * g) (h₂ : g * b₁ = b₁ * g) (h₃ : g * a₂ = a₂ * g)
    (h₄ : g * b₂ = b₂ * g) (hsyl : IsSylowIn 2 (centIn ⊤ A) A) : False := by
  have hgy : ∀ y : G, π y ∈ A → g * y = y * g := by
    intro y hy
    have hle : Subgroup.closure (({a₁, b₁, a₂, b₂} : Set G) ∪ ((π.ker : Subgroup G) : Set G)) ≤
        Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hz with hz | hz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact h₁
        · exact h₂
        · exact h₃
        · exact h₄
      · exact (hcen z hz h).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle (hgen y hy))) g (Set.mem_singleton g)
  have hs2 : π g * π g = 1 := by
    rw [← map_mul, hg2, map_one]
  have hsc : ∀ a ∈ A, a * π g = π g * a := by
    intro a ha
    obtain ⟨y, rfl⟩ := hπs a
    rw [← map_mul, ← map_mul, (hgy y ha).symm]
  have hsA : π g ∉ A := by
    intro hsA
    by_cases hs1 : π g = 1
    · exact hgn (MonoidHom.mem_ker.mpr hs1)
    · obtain ⟨y, hyA, hy⟩ := hP2 g hsA hs1
      have h1 : ⁅g, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hgy y hyA)
      exact hm1 (hy.symm.trans h1)
  exact l2_not_sylow_of_extra hsc hsA hs2 hsyl

end CFSG.OddStandard.HigherRank.YamadaG23
