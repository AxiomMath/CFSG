module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10Normalized
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueSetting
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueShape
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueFactor
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GluePlace

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.AGLEmbedding
  CFSG.Open

theorem k5192P2_of_atM
    (h : ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
      (∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → Nonempty (L ≃* alternatingGroup (Fin 5))) →
      ∀ T₁ T₂ : Subgroup X, IsC118Pair T T₁ T₂ → GNFactor T T₁ T₂ ∧ GNShape T T₁ T₂) :
    K5192P2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv he
  obtain ⟨P₂, hPL, hP, hTP⟩ := A10TwoFourSFiveNormalized Ls (gnImg T T) he hinv
    (hX.sylow.2.1.map (toStar T))
  refine ⟨P₂, hPL, hP, ?_⟩
  have hTM : T ≤ (oddHull P₂ ⊔ gnImg T T).comap (toStar T) := fun t ht =>
    Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ ht))
  have hgn := gnSetting_oddHull_sup_gnImg hX he hPL hP hTP
  have hne : T.subgroupOf ((oddHull P₂ ⊔ gnImg T T).comap (toStar T)) ≠ ⊥ := by
    intro hbot
    exact hX.ne_bot_of_isComponentOf hY.1
      ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hTM)
  have halt : ∀ L : Subgroup (↥((oddHull P₂ ⊔ gnImg T T).comap (toStar T)) ⧸
      gnC (T.subgroupOf ((oddHull P₂ ⊔ gnImg T T).comap (toStar T)))), IsComponentOf L ⊤ →
      Nonempty (L ≃* alternatingGroup (Fin 5)) := fun _ hL =>
    nonempty_mulEquiv_alt_five_of_isComponentOf hX.sylow hP hTP hL
  obtain ⟨hfac, hshape⟩ := h _ _ hgn hne halt _ _ (hGood.c118.subgroupOf hTM)
  exact oddHull_le_gnA_of_forall_mul hX.sylow hGood.c118 hPL hP hTP
    (exists_mul_of_gnFactor_of_ystar_eq_bot hTM hGood.c118 hfac
      (ystar_eq_bot_of_gnShape_of_alt_five hshape halt))

end CFSG.LocalAnalysis.RankThreeUC.S15

end
