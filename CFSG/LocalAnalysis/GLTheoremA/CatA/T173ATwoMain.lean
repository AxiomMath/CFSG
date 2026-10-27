module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

section Holds


theorem t173ALinTwo_holds : T173ALinTwo := by
  intro p Ω _ _ S B N D K x d F _ _ θ hcfg hcat hmark
  obtain ⟨hF, hd3, hp3⟩ := lin_two_params hcfg.prime hmark
  subst hp3
  obtain ⟨e⟩ := lin_two_equiv_vecAut (d := d) (F := F) hF
  have hBin := lin_two_B_le_sup hcfg.normal hcfg.qs hF hmark
  obtain ⟨M⟩ := S172X.S172Model.nonempty_of_mem_sup hcfg.normal hBin (θ.trans e)
  have h6 : 6 ≤ d := by
    have := lin_two_six_le (V := Fin d → ZMod 2) hcfg M
    simpa using this
  have hZ0 : Subgroup.center ↥S = ⊥ := lin_two_center_bot hcfg.qs hF (by omega) θ
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥S) := by
    rw [hZ0, Subgroup.card_bot]
    norm_num
  have hfact := lin_two_hfact (V := Fin d → ZMod 2)
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (by simpa using h6)
  exact T173X.concl_of_trichotomy hcfg M hZ hfact

end Holds

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
