module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint

theorem LieModel.nonempty_mulEquiv_SL_three_two {X : Type} [Group X] (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K
      (by rw [hcard]; norm_num))⟩
  all_goals exact absurd h0 (by norm_num)

end CFSG.Blueprint
