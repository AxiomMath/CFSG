module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem natGenProp
    : NatGenProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc hres had hq
  classical
  have hS := ctx.setting
  have hout := even_SL2_natural_baumann hS ctx.comps ctx.natural
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hbase := hloc.base
  have hbasic := hloc.basic
  have hSP : baum R ≤ P := hbasic.lt.le
  have hPLS := hres.le_LS
  have hLn := natL_normal (G := G)
  have hLN : (⊤ : Subgroup G) ≤
      Subgroup.normalizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G) := by
    intro g _
    have := hLn
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hRTn : R ≤ Subgroup.normalizer (baum R : Set G) := fun t ht =>
    mem_normalizer_of_characteristic hbase.S_char inf_le_left (Subgroup.le_normalizer ht)
  have hblk : ∀ _ : Fin 1, IsBlock2 P (oddOrderSubgroup P) := fun _ => had.chi0.1
  have hgen : baum R ⊔ ⨆ _ : Fin 1, oddOrderSubgroup P = P := by
    rw [iSup_const, sup_comm]
    exact hres.P_eq.symm
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := normal_Sylow_part_block_centrality (X := ⊤) (T := R)
    (N := oddOrderSubgroup (⊤ : Subgroup G)) (R := baum R) (P := P) hS.sylow le_top hLN
    hbridge.X_eq.symm (hasNoTwoQuotient_oddOrderSubgroup ⊤) inf_le_left hRTn hout.sylow
    hbase.charTwo hSP hPLS hbasic.gen (s := 1) le_rfl (fun _ => oddOrderSubgroup P) hblk hgen
  refine ⟨h1.trans iSup_const, h2, h3, ?_, ?_⟩
  · exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h4)
  · rw [BlueprintB2.omegaOneCenterOf_eq_centerTorsion]
    exact h5

end CFSG.QuasithinUnique.Setup.Lift
