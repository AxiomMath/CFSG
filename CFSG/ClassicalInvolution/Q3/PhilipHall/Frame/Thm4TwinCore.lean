module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinFields
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOMain
public import CFSG.ClassicalInvolution.Q3.TL3T34

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform

theorem Thm4Twin.f2CoreConfig_of_f2Config {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}
    (h : Thm4Twin.F2Config J L L₀) : TL4.F2CoreConfig J L L₀ := by
  obtain ⟨hm, hgen, -, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩ := h
  exact ⟨hm.hyp, hm.notConj, hm.notComm, hgen, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩

theorem Thm4Twin.exitModel_of_core {n : ℕ} (h : TL4.ExitModelCore n) :
    Thm4Twin.Thm4TwinF.ExitModel n :=
  fun G _ _ hG J L L₀ hc K hK z hz hout =>
    h G hG J L L₀ (Thm4Twin.f2CoreConfig_of_f2Config hc) K hK z hz hout


theorem thm4RTwin_of_core
    (hX : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TL4.ExitModelCore n) :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n :=
  thm4RTwin_of_cit3Below (TC.Thin.d1GenLeaf_holds 3)
    (fun n hA hP => Thm4Twin.exitModel_of_core (hX n hA hP))
    (fun n hA hP => TL4.exitModelR_of_core (hX n hA hP))

theorem thm4RTwin_of_twoClass
    (hX : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TL4.ExitTwoClassR n) :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n :=
  thm4RTwin_of_core fun n hA hP => TL4.exitModelCore_of hA hP (hX n hA hP)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
