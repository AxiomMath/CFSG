module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSUCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModel

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem SU42b_eq_suClosure : SU42b = Certificates.suClosure := by
  unfold SU42b Certificates.suClosure
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (coe_genGL 0)
    · exact Or.inr (coe_genGL 1)
  · rintro (h | h)
    · exact Or.inl (Units.ext (h.trans (coe_genGL 0).symm))
    · exact Or.inr (Units.ext (h.trans (coe_genGL 1).symm))

theorem card_SU42b : Nat.card SU42b = 25920 := by
  rw [SU42b_eq_suClosure, card_suClosure_eq]

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
