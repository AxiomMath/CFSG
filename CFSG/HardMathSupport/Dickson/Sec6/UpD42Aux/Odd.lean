module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.SimpleType
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Odd
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.PumpDefChar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416ROdd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremA

section


theorem upD42OddLeaf_holds : UpD42OddLeaf := by
  intro S _ _ hS hnab d hd ⟨e⟩ α hpump
  obtain ⟨hα3, hα1, I, hI, hI42⟩ := hpump
  have hchar : d.1.characteristic ≠ 2 := characteristic_ne_two_of_not_isCharTwoLieIndex hd
  have hprime : d.1.characteristic.Prime := d.characteristic_prime
  have hChev : IsChevSimple d.1.characteristic S := Or.inl ⟨.lie d, rfl, ⟨e⟩⟩
  have hChevDown : IsChevSimple d.1.characteristic (PSimple 3 I) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.PumpDefChar.kdChevDownQ_odd
      Nat.prime_three (by decide) d.1.characteristic S hS hnab hChev α hα3 I hI
  have h42 : IsCatalogLieIso (PSimple 3 I) IsD42Index := isD42_pSimple hI42
  have h2 : IsChevSimple 2 (PSimple 3 I) := isChevSimple_two_of_isD42 h42
  have hsmall : catalogIs (PSimple 3 I) CFSG.LocalAnalysis.GLTheoremA.chev2Small :=
    chev2OddAmb_holds d.1.characteristic (PSimple 3 I) hprime hchar h2 hChevDown
  exact not_catalogIs_chev2Spor_of_isD42 lieOrderBridge_holds h42
    (catalogIs_chev2Spor_of_small hsmall)

end

end CFSG.HardMathSupport.Dickson.Sec6

end
