module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Coxeter
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Open TauCeti.Sporadic

@[expose] def babyMonsterEdges : List (Fin 11 × Fin 11) :=
  [(4, 3), (3, 2), (2, 1), (1, 0), (4, 5), (5, 6), (6, 7), (4, 8), (8, 9), (9, 10)]

@[expose] def babyMonsterSepFst : Fin 4 → Fin 11 := ![4, 1, 6, 9]

@[expose] def babyMonsterSepSnd : Fin 4 → Fin 11 := ![3, 0, 7, 10]

theorem exists_isElemAbelian_three_of_mulEquiv_B {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.B.Group) (hG : ∃ g h : G, g * h ≠ h * g) {r : ℕ}
    (hr : r ≤ 4) : ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  refine Coxeter.exists_isElemAbelian_three_of_coxeterRelations babyMonsterEdges
    BabyMonster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 4 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel)) PresentedGroup.of
    (PresentedGroup.closure_range_of _)
    (fun i j => Coxeter.presentedGroup_coxeter_pow_eq_one _ _ i j) (K := ⊤) le_top
    (e.trans (BabyMonster.mulEquivPresentedGroupCoxeterAppend.trans Subgroup.topEquiv.symm)) hG hr
    babyMonsterSepFst babyMonsterSepSnd (by decide +kernel) (by decide +kernel)
  rw [BabyMonster.coxeterMatrix_apply, BabyMonster.edges_eq]
  rfl

theorem exists_isElemAbelian_three_pow_four_of_mulEquiv_B {G : Type*} [Group G]
    (e : G ≃* TauCeti.SporadicName.B.Group) (hG : ∃ g h : G, g * h ≠ h * g) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  exists_isElemAbelian_three_of_mulEquiv_B e hG le_rfl

theorem tcExcludedSporadic_B : TCExcludedSporadic .B := by
  intro G _ _ _ hG ⟨e⟩
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_three_of_mulEquiv_B e hG (r := 3) (by norm_num)
  exact ⟨3, Nat.prime_three, by norm_num, E, hE, hcard⟩

end CFSG.QuasithinUnique.SQTK
