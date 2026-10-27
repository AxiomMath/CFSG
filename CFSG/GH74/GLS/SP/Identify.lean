module

public import CFSG.GH74.BNPair.Coordinatization

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair

universe u

section Xplus

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem root_le_Xplus {i : ℤ} (hi : IsRoot n i) : D.root i ≤ D.Xplus := fun _ hx =>
  Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩)

theorem xplus_eq_top [IsSimpleGroup X] : D.Xplus = ⊤ := by
  have hn : D.Xplus.Normal := eq30_3.{u} X n D
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D.Xplus with h | h
  · exfalso
    have h1 : IsRoot n 1 :=
      ⟨one_ne_zero, show 1 ≤ n by have := D.three_le; omega⟩
    apply D.roots.ne_bot 1 h1
    rw [eq_bot_iff, ← h]
    exact root_le_Xplus D h1
  · exact h

end Xplus

theorem nonempty_mulEquiv_of_rankTwo {G G' : Type u} [Group G] [Group G'] [IsSimpleGroup G]
    [IsSimpleGroup G'] {n : ℕ} (D : RankTwoSystem G n) (D' : RankTwoSystem G' n) (φ : D.U ≃* D'.U)
    (hφ : ∀ i : ℤ, 1 ≤ i → i ≤ n → ∀ x : D.U, (x : G) ∈ D.root i ↔ ((φ x : D'.U) : G') ∈ D'.root i) :
    Nonempty (G ≃* G') := by
  obtain ⟨e⟩ := theorem30_4.{u} G G' n D D' φ hφ
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr (xplus_eq_top D).symm).trans
    (e.trans ((MulEquiv.subgroupCongr (xplus_eq_top D')).trans Subgroup.topEquiv)))⟩

end CFSG.GH74.GLS.SP
