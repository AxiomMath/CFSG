module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

import TauCeti.LinearAlgebra.Matrix.Commute

public section

namespace CFSG.ClassicalGroups.SpecialLinear.TvMod

open Module CFSG.RankThree.OrthogonalInvolutions

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem commute_of_commute_of_finrank_eq_two (hV : finrank K V = 2) {f g h : Module.End K V}
    (hf : ∀ c : K, f ≠ c • 1) (hg : Commute f g) (hh : Commute f h) : Commute g h := by
  have : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq K V hV)
  have hne : e f ∉ Set.range (Matrix.scalar (Fin 2)) := by
    rintro ⟨c, hc⟩
    refine hf c (e.injective ?_)
    rw [← hc, map_smul, map_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  exact Commute.of_map e.injective (TauCeti.commute_of_commute_fin_two hne (hg.map e) (hh.map e))

end Field

end CFSG.ClassicalGroups.SpecialLinear.TvMod
