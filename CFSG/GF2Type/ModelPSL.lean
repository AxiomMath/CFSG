module

public import CFSG.Blueprint.Catalog
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem lieModel_psl_two_of_mulEquiv {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n)
    (e : G ≃* PSL(n, ZMod 2)) : LieModel G .PSL n 2 1 := by
  refine Or.inl ⟨by simp [classicalTags], ⟨Nat.prime_two, le_rfl, ?_, ?_, ?_⟩,
    ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj n (ZMod 2))⟩⟩
  · omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

end CFSG.GF2Type
