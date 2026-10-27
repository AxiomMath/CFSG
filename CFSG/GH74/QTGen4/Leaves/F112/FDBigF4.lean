module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.GH74.QTGen4.U42.VertexGen4
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7Top
public import CFSG.Quasithin.EmptyFaithful.S152ZFMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input15204F112_holds : CFSG.Quasithin.He9.Input15204F112 :=
  CFSG.Quasithin.He9.input15204F112_of_untw
    CFSG.Quasithin.Kleidman.F204.input15204F112Untw_holds

theorem f112_fd_big_false_finite4 :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VFD L1 → VBig L2 → False := by
  intro G _ _ L1 L2 S h hFD hBig
  have hns : ¬ Group.IsSolvable ↥L2 := (F112Hyp.vBig_iff_right h).1 hBig
  have hq : IsL2Quot 2 (oTwoQuot ↥L2) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4
      (CFSG.GH74.QTGen4.Finite4.gen4 (G := G)) h.1.h2 hns
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  exact input15204F112_holds G L1 L2 S h.1 h.2.1 h.2.2 hFD ⟨e⟩

end CFSG.Quasithin
