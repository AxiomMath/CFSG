module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416L
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110m

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance

theorem isD42_pSimple {G : Type} [Group G] {I : Subgroup G}
    (h : IsCatalogLieIso (↥I ⧸ GLAPPrimeCore 3 ↥I) IsD42Index) :
    IsCatalogLieIso (PSimple 3 I) IsD42Index := by
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_isD42Type h
  haveI := hs
  have hcen : Subgroup.center (barOf 3 I) = ⊥ := up34_center_eq_bot_of_simple hnab
  exact IsCatalogLieIso.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm h

theorem isChevSimple_two_of_isD42 {Q : Type} [Group Q] (h : IsCatalogLieIso Q IsD42Index) :
    IsChevSimple 2 Q := by
  obtain ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩ := h
  refine Or.inl ⟨.lie ⟨idx, hv⟩, ?_, ⟨e⟩⟩
  cases idx with
  | D r q =>
    simp only [IsD42Index] at hd
    show (TauCeti.LieTypeIndex.D r q).characteristic = 2
    rw [TauCeti.LieTypeIndex.characteristic_D, hd.2.1]
  | _ => exact absurd hd (by simp [IsD42Index])

theorem not_catalogIs_chev2Spor_of_isD42 (hb : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    (h : IsCatalogLieIso Q IsD42Index) :
    ¬ catalogIs Q CFSG.LocalAnalysis.GLTheoremA.chev2Spor := by
  intro hc
  have hle :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m.card_le_of_catalogIs_chev2Spor_d4cls
      hb hc
  rw [card_of_isD42Type h] at hle
  norm_num at hle

end CFSG.HardMathSupport.Dickson.Sec6

end
