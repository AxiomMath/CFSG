module

public import CFSG.LieType.Universal.RootData

public section

namespace CFSG.LieType.Universal

theorem UniversalRootDatum.not_mem_roots_of_rank_eq_zero {K : Type*} [Group K]
    (D : UniversalRootDatum K) (h : D.rank = 0) {γ : Fin D.rank → ℤ} : γ ∉ D.roots := by
  intro hγ
  rcases (show γ ∈ RootSystem.roots D.isFiniteType D.divisible from hγ) with
    ⟨w, i, -⟩ | ⟨w, i, -, -⟩
  · exact absurd (Fin.pos i) (by omega)
  · exact absurd (Fin.pos i) (by omega)

end CFSG.LieType.Universal
