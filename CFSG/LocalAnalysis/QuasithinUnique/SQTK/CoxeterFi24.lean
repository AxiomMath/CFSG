module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Coxeter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open TauCeti.Sporadic

@[expose] def fi24CoxeterEdges : List (Fin 12 × Fin 12) :=
  [(11, 10), (10, 0), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)]

@[expose] def fi24SepFst : Fin 4 → Fin 12 := ![11, 1, 4, 7]

@[expose] def fi24SepSnd : Fin 4 → Fin 12 := ![10, 2, 5, 8]

theorem exists_isElemAbelian_three_of_mulEquiv_Fi24Prime {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.Fi24Prime.Group) (hG : ∃ g h : G, g * h ≠ h * g) {r : ℕ}
    (hr : r ≤ 4) : ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  refine Coxeter.exists_isElemAbelian_three_of_coxeterRelations fi24CoxeterEdges
    fi24AutomorphismCoxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 11 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _) fi24AutomorphismGroup_of_mul_of_pow
    (K := commutator Fi24AutomorphismGroup) le_rfl (e.trans fi24PrimeGroupMulEquivCommutator) hG hr
    fi24SepFst fi24SepSnd (by decide +kernel) (by decide +kernel)
  rw [fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def]
  rfl

theorem exists_isElemAbelian_three_pow_four_of_mulEquiv_Fi24Prime {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.Fi24Prime.Group) (hG : ∃ g h : G, g * h ≠ h * g) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  exists_isElemAbelian_three_of_mulEquiv_Fi24Prime e hG le_rfl

theorem tcExcludedSporadic_Fi24Prime : TCExcludedSporadic .Fi24Prime := by
  intro G _ _ _ hG ⟨e⟩
  obtain ⟨E, hE, hcard⟩ :=
    exists_isElemAbelian_three_of_mulEquiv_Fi24Prime e hG (r := 3) (by norm_num)
  exact ⟨3, Nat.prime_three, by norm_num, E, hE, hcard⟩

end CFSG.QuasithinUnique.SQTK
