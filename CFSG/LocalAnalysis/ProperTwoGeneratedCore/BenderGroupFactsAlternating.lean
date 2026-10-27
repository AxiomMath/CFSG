module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ProperTwoGeneratedCore.BenderFacts

open Equiv CFSG.ComponentClassification.OuterAutomorphisms CFSG.BenderSuzuki.MatrixGroups

theorem nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five :
    Nonempty (PSL2BinaryMatrixGroup 2 ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := GaloisField.card 2 2 (by norm_num)
  have : Finite (GaloisField 2 2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hcard)
  exact ⟨(CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    (GaloisField 2 2)).trans e⟩

theorem card_outer_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (Outer (alternatingGroup (Fin n))) = 2 := by
  set c : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin n)) with hc
  have hbij : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have hrange : inner (alternatingGroup (Fin n)) = (alternatingGroup (Fin n)).map c := by
    ext φ
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g, g.2, ?_⟩
      ext x
      simp [hc]
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨⟨σ, hσ⟩, ?_⟩
      ext x
      simp [hc]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [← Subgroup.index_eq_card, hrange, Subgroup.index_map_eq _ hbij.2,
    alternatingGroup.index_eq_two]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [hbij.1 (hσ.trans (map_one c).symm)]
  exact one_mem _

theorem card_outer_eq_two_of_mulEquiv_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {J : Type*} [Group J] (e : J ≃* alternatingGroup (Fin n)) : Nat.card (Outer J) = 2 := by
  rw [Nat.card_congr (equivalence e).toEquiv, card_outer_alternatingGroup hn hn6]

theorem card_outer_eq_two_of_mulEquiv_alternatingGroup_five {J : Type*} [Group J]
    (e : J ≃* alternatingGroup (Fin 5)) : Nat.card (Outer J) = 2 :=
  card_outer_eq_two_of_mulEquiv_alternatingGroup (by norm_num) (by norm_num) e

theorem card_outer_eq_two_of_mulEquiv_psl2Binary_two
    {J : Type*} [Group J]
    (e : J ≃* PSL2BinaryMatrixGroup 2) : Nat.card (Outer J) = 2 := by
  obtain ⟨e₅⟩ := nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
  exact card_outer_eq_two_of_mulEquiv_alternatingGroup_five (e.trans e₅)

theorem card_outer_eq_two_of_mulEquiv_alternatingGroup_seven {J : Type*} [Group J]
    (e : J ≃* alternatingGroup (Fin 7)) : Nat.card (Outer J) = 2 :=
  card_outer_eq_two_of_mulEquiv_alternatingGroup (by norm_num) (by norm_num) e

theorem isSolvable_outer_of_mulEquiv_alternatingGroup_seven {J : Type*} [Group J]
    (e : J ≃* alternatingGroup (Fin 7)) : Group.IsSolvable (Outer J) := by
  have := CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_solvable_outside_six
    (n := 7) (Or.inr le_rfl)
  exact solvable_of_equiv e.symm

end CFSG.ProperTwoGeneratedCore.BenderFacts
