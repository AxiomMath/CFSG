module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterUntw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterTriD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen


theorem genNormalExcOuter_holds : GenNormalExcOuter := by
  intro p T _ _ d h hd x hx hx1 hout
  obtain ⟨e⟩ := h.iso
  refine compNormal_of_compsNormal ?_
  have hc2 := h.charOdd
  have hpc := h.ne
  obtain ⟨d, hv⟩ := d
  cases d with
  | G2 q =>
    exact compsNormal_untw_cat (τ := .G2) (Or.inl rfl) (c := TauCeti.LieTypeIndex.G2)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_G2] using hc2) e h.prime h.odd x hx hx1 hout
  | F4 q =>
    exact compsNormal_untw_cat (τ := .F4) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_F4] using hc2) e h.prime h.odd x hx hx1 hout
  | E6 q =>
    exact compsNormal_untw_cat (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_E6] using hc2) e h.prime h.odd x hx hx1 hout
  | E7 q =>
    exact compsNormal_untw_cat (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_E7] using hc2) e h.prime h.odd x hx hx1 hout
  | E8 q =>
    exact compsNormal_untw_cat (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_E8] using hc2) e h.prime h.odd x hx hx1 hout
  | twistedE6 q => exact compsNormal_twE6_cat q hv e h.prime h.odd x hx hout
  | trialityD4 q =>
    exact compsNormal_triD4_cat q hv
      (by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hc2) e h.prime h.odd
      (by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hpc) x hx hout
  | _ => simp [S2019.S2019ExcCoreIdx] at hd

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
