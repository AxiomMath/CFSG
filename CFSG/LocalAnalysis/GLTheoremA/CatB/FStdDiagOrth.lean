module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSympModels
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthData
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamOrth)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem smallFam_orth : SmallFam CFSG.LocalAnalysis.GLTheoremA.Y10GField.FamOrth := by
  intro S _ _ labK α I hFam hcen hα3 hα1 hin hI hord
  obtain ⟨t, m, n, a, ht, hm, hn, hG, ha3, ha1, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsOrthData hcen hFam hα3 hα1 hin
  obtain ⟨X, _, _, hXL, hfac, -, g, hg, hker⟩ :=
    exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
      omegaFactorField_holds Nat.prime_three (by decide) (Or.inr ht) hG (by decide) a ha3 I hI
  have hQ := fstdSymp_quot_equiv hXL.perfect g hg hker
  unfold OrthFactorOver at hfac
  rcases hfac with ⟨b, j, E, _, _, hb2, hj, -, hcard, hb4, ⟨eX⟩⟩ |
    ⟨b, j, q', E, _, _, hb3, hj, -, hq', hcard, hbq, ⟨eX⟩⟩ |
    ⟨K', _, _, hK', -, s, hs2, hne, ⟨eX⟩⟩ |
    ⟨K', _, _, V, _, _, _, Q, hK', -, hQd, hd, hT, ⟨eX⟩⟩
  ·
    have hE : Nat.card E = 2 ^ (n * j) := by
      rw [Nat.card_eq_fintype_card, hcard, pow_mul]
    exact (fstdSymp_sl_false hord hQ hb2 (Nat.mul_pos hn hj) hE
      (fun h => by rw [Nat.card_eq_fintype_card]; exact hb4 h) eX).elim
  ·
    have hq'' : q' = 2 ^ (n * j) := by rw [hq', pow_mul]
    subst hq''
    have hE : Nat.card E = (2 ^ (n * j)) ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]
    obtain ⟨-, -, hc, hZ⟩ := fstdSymp_su_case hord hQ hb3 (Nat.mul_pos hn hj) hbq hE eX
    refine ⟨?_, fun h360 => ?_⟩
    · rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective
        hXL.perfect g hg hker, hZ, Subgroup.map_bot]
    · rw [hc] at h360
      omega
  ·
    exact (fstdSymp_sp_false hord hQ hs2 hn hK' (fun h => hne (by rw [h.1, h.2])) eX).elim
  ·
    exact (fstdSymp_omega_false hord hQ hK' hQd hd hT eX).elim

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
