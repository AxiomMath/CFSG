module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear

public section

namespace CFSG.ComponentClassification.CatalogueBGeneralLinear

noncomputable section

universe u

theorem generalLinear_one_solvable (K : Type u) [Field K] :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 1) K) := by
  let : Subsingleton (specialLinearRange 1 K) :=
    (rangeEquivSpecialLinear 1 K).toEquiv.subsingleton
  let : Group.IsSolvable
      (Matrix.GeneralLinearGroup (Fin 1) K ⧸ specialLinearRange 1 K) :=
    determinantQuotient_solvable 1 K
  exact Group.isSolvable_of_subgroup_quotient (specialLinearRange 1 K)

theorem projectiveGeneralLinear_two_small_solvable (K : Type u) [Field K] [Finite K]
    (hcard : Nat.card K = 2 ∨ Nat.card K = 3) :
    Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) K) := by
  let : Group.IsSolvable (Equiv.Perm (CatalogueSchreierLinearTwo.Omega K)) :=
    Equiv.Perm.isSolvable (by
      change Nat.card (Option K) ≤ 4
      rw [Finite.card_option]
      omega)
  exact Group.isSolvable_of_isSolvable_injective
    (CatalogueSchreierLinearTwo.coordinatePGLAction_injective K)

theorem generalLinear_two_small_solvable (K : Type u) [Field K] [Finite K]
    (hcard : Nat.card K = 2 ∨ Nat.card K = 3) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) := by
  let : Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) K) :=
    projectiveGeneralLinear_two_small_solvable K hcard
  exact Group.isSolvable_of_ker_le_range
    (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).subtype
    Matrix.ProjGenLinGroup.mk (by
      rw [Matrix.ProjGenLinGroup.ker_mk, Subgroup.range_subtype])

theorem no_pComponent_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (p : ℕ) (L : Subgroup G) : ¬ CFSG.IsPComponent p L := by
  intro hL
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem generalLinear_small_solvable (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hsmall : n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin n) K) := by
  rcases hsmall with rfl | ⟨rfl, hcard⟩
  · exact generalLinear_one_solvable K
  · exact generalLinear_two_small_solvable K hcard

theorem generalLinear_small_no_pComponent (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hsmall : n = 1 ∨ n = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3))
    (p : ℕ) (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin n) K) :=
    generalLinear_small_solvable n K hsmall
  exact no_pComponent_of_solvable p L

end

end CFSG.ComponentClassification.CatalogueBGeneralLinear
