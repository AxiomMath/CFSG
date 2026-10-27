module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem KD264F8KerLn_holds : KD264F8KerLn := by
  unfold KD264F8KerLn KD264F8Kernel
  intro d _hfin _hns _hk2 _hk3 _hov hP A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨n, q, rfl, hn3, hn6, hq⟩ := hP
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : (TauCeti.CFSGIndex.lie ⟨.A n q, hd1⟩).Group ≃*
      projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd1).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _)
  have hcardK : Nat.card (GaloisField q.p q.exponent) = 8 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    exact hq
  obtain ⟨hAab, hout, hnot⟩ := F8Trans.hyp_transport e A hA
  exact F8Trans.datum_of_equiv e A (F8Ln.kerLn_model (by omega) hcardK _ hAab hout hnot)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
