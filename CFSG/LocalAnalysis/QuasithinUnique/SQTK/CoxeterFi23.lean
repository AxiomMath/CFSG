module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Coxeter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open TauCeti.Sporadic

@[expose] def fi23CoxeterEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)]

@[expose] def fi23SepFst : Fin 3 → Fin 10 := ![0, 3, 6]

@[expose] def fi23SepSnd : Fin 3 → Fin 10 := ![1, 4, 9]

theorem exists_isElemAbelian_three_of_mulEquiv_Fi23 {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.Fi23.Group) (hG : ∃ g h : G, g * h ≠ h * g) {r : ℕ}
    (hr : r ≤ 3) : ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  refine Coxeter.exists_isElemAbelian_three_of_coxeterRelations fi23CoxeterEdges
    fi23CoxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _)
    (fun i j => Coxeter.presentedGroup_coxeter_pow_eq_one _ _ i j) (K := ⊤) le_top
    (e.trans (fi23MulEquivPresentedGroupCoxeterAppend.trans Subgroup.topEquiv.symm)) hG hr
    fi23SepFst fi23SepSnd (by decide +kernel) (by decide +kernel)
  rw [fi23CoxeterMatrix_apply, fi23Edges_def]
  rfl

theorem exists_isElemAbelian_three_pow_three_of_mulEquiv_Fi23 {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.Fi23.Group) (hG : ∃ g h : G, g * h ≠ h * g) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 :=
  exists_isElemAbelian_three_of_mulEquiv_Fi23 e hG le_rfl

theorem tcExcludedSporadic_Fi23 : TCExcludedSporadic .Fi23 := by
  intro G _ _ _ hG ⟨e⟩
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_three_pow_three_of_mulEquiv_Fi23 e hG
  exact ⟨3, Nat.prime_three, by norm_num, E, hE, hcard⟩

end CFSG.QuasithinUnique.SQTK
