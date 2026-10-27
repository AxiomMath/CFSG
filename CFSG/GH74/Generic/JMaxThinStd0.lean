module

public import CFSG.GH74.Generic.JMaxThinFromStage1
public import CFSG.GH74.GLS.Stage1.Main.Assembly
public import CFSG.GH74.GLS.Stage2.Local.Prop27WComps

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage2.Local.Prop28

theorem thinStage1Interface_of_std0
    (hOut3 : Stage1OutThree) (hOut4 : Stage1OutFour) (h27 : Leaf_Prop27W Stage2Ctx0) :
    ThinStage1Interface := by
  refine thinStage1Interface_of_leaves (fun G _ _ => Std0 G)
    (fun G _ _ z k S => Stage2Ctx0 G z k S ∧ k ≠ Kind.m12)
    (fun G _ _ hs hg hK hn h3' h4' => ⟨hs, hg, hK, ⟨h3', h4'⟩, hn⟩)
    (fun G _ _ z k S h => h.1.data)
    (fun G _ _ hs h hT => ?_) (fun G _ _ hs h hT => ?_)
    (fun G _ _ z k S h y hy => compsGood_of_leaf_prop27W h27 G z k S h.1 h.2 y hy)
  · obtain ⟨z, S, hz, hS, hout⟩ := hOut3 _ hs h hT
    exact ⟨z, S, hz, hS, hout.ctx, by simp⟩
  · obtain ⟨z, S, k, hk, hz, hS, hout⟩ := hOut4 _ hs h hT
    exact ⟨z, S, k, hk, hz, hS, hout.ctx, by rcases hk with rfl | ⟨ε, rfl⟩ | rfl | rfl <;> simp⟩

theorem s_corTwoThinGen4_of_std0
    (hOut3 : Stage1OutThree) (hOut4 : Stage1OutFour) (h27 : Leaf_Prop27W Stage2Ctx0) :
    S_corTwoThinGen4 :=
  s_corTwoThinGen4_of_thinStage1Interface (thinStage1Interface_of_std0 hOut3 hOut4 h27)

end CFSG.GH74.Generic
