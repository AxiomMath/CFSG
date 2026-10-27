module

public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_alternating_six_of_statedProj {S : Type} [Group S] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 9) (e : S ≃* StatedProj (StatedSL 2 K)) :
    Nonempty (S ≃* ↥(alternatingGroup (Fin 6))) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      K (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans φ⟩

theorem nonempty_mulEquiv_alternating_six_of_psl_two_nine {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 3 2) : Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact nonempty_mulEquiv_alternating_six_of_statedProj (by rw [hK]; norm_num) e

end CFSG.Open.StatedAPI

namespace CFSG.Blueprint

theorem LieModel.nonempty_mulEquiv_alternating_six {X : Type} [Group X]
    (h : LieModel X .PSL 2 3 2) : Nonempty (X ≃* alternatingGroup (Fin 6)) :=
  Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine
    (h.statedClassicalModel (by decide))

end CFSG.Blueprint
