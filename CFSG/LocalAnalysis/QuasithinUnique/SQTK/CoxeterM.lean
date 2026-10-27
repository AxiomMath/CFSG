module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Coxeter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open TauCeti.Sporadic

@[expose] def monsterEdges : List (Fin 12 × Fin 12) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7), (7, 8), (0, 9), (9, 10), (10, 11)]

@[expose] def monsterSepFst : Fin 4 → Fin 12 := ![0, 3, 6, 10]

@[expose] def monsterSepSnd : Fin 4 → Fin 12 := ![1, 4, 7, 11]

theorem exists_isElemAbelian_three_of_mulEquiv_M {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.M.Group) (hG : ∃ g h : G, g * h ≠ h * g) {r : ℕ}
    (hr : r ≤ 4) : ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  refine Coxeter.exists_isElemAbelian_three_of_coxeterRelations monsterEdges
    Monster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _)
    (fun i j => Coxeter.presentedGroup_coxeter_pow_eq_one _ _ i j) (K := ⊤) le_top
    (e.trans (Monster.mulEquivPresentedGroupCoxeterAppend.trans Subgroup.topEquiv.symm)) hG hr
    monsterSepFst monsterSepSnd (by decide +kernel) (by decide +kernel)
  rw [Monster.coxeterMatrix_apply, Monster.edges_def]
  rfl

theorem exists_isElemAbelian_three_pow_four_of_mulEquiv_M {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.M.Group) (hG : ∃ g h : G, g * h ≠ h * g) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  exists_isElemAbelian_three_of_mulEquiv_M e hG le_rfl

theorem tcExcludedSporadic_M : TCExcludedSporadic .M := by
  intro G _ _ _ hG ⟨e⟩
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_three_of_mulEquiv_M e hG (r := 3) (by norm_num)
  exact ⟨3, Nat.prime_three, by norm_num, E, hE, hcard⟩

end CFSG.QuasithinUnique.SQTK
