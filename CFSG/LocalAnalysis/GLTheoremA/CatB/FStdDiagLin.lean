module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagLinBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinDichot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin)
open CFSG.LocalAnalysis.GLTheoremA.K1419

theorem smallFam_lin : SmallFam FamLin := by
  intro S _ _ labK α I hFam hcen hα3 hα1 hin hI hsmall
  exfalso
  have hI3 := fstdLin_glaPComponent hI hsmall
  obtain ⟨K, hK, hKf, d, A, u, J', h2, hd, ⟨k, hk⟩, hu, hpow, hAns, hJ', ⟨ePQ⟩⟩ :=
    k1419ClsLinData hcen hFam hα3 hα1 hin hI3
  obtain ⟨M, hM, ⟨ePS⟩, -⟩ := k1419ClsLinLift h2 hd A u hu hpow J' hJ'
  obtain ⟨c, hc⟩ := Y10GInnLin.isScalar_of_pow_trivial h2 A 3 u hu hpow
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩, -⟩ := k1419ClsLinDichot h2 hd A ⟨c, hc⟩ hAns M hM
  have hEcard : Nat.card E = 2 ^ (k * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hk, ← pow_mul]
  have e1 : PSimple 3 I ≃* StatedProj (StatedSL a E) :=
    (QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)).trans (ePS.trans eM)
  have hcard := Nat.card_congr e1.toEquiv
  obtain ⟨h25920, h360⟩ := fstdLin_card_psl_ne ha hEcard
  rcases fstdLin_card_pSimple hI.2.2 hsmall with h | h
  · exact h25920 (hcard.symm.trans h)
  · exact h360 (hcard.symm.trans h)

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
