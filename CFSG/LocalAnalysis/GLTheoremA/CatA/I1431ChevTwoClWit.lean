module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.RankThree.PartTwo.Census.Spin TauCeti

theorem Local81.of_hasWitness {G : Type} [Group G] (h : HasWitness G 3 4) : Local81 G := by
  obtain ⟨E, P, hE, hEp, hc, hP, hP2, hEN⟩ := h
  exact ⟨P, hP2, hP, E, hEN, ⟨hE, hEp⟩, hc⟩

theorem local81_B (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) (hp : q.p = 2)
    (h5 : 5 ≤ r) : Local81 (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := typeB_mk_data r q hv
  exact Local81.of_hasWitness (CarrierB.hasWitness_short _ (hchar.trans hp) (by omega))

theorem local81_D (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) (hp : q.p = 2)
    (h5 : 5 ≤ r) : Local81 (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  obtain ⟨hchar, -, -, hrank⟩ := typeD_mk_data r q hv
  rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h6
  · exact Local81.of_hasWitness
      (CarrierD.hasWitness_five _ (hchar.trans hp) (by rw [hrank]; exact h))
  · exact Local81.of_hasWitness
      (CarrierD.hasWitness_three _ (hchar.trans hp) (by rw [hrank]; exact h6))

theorem local81_twistedD (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) (h5 : 5 ≤ r) :
    Local81 (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  obtain ⟨hchar, -, hexp, hrank⟩ := typeTwistedD_mk_data r q hv
  rcases (show r = 5 ∨ 6 ≤ r by omega) with h | h6
  · exact Local81.of_hasWitness (CarrierTD.hasWitness_tdfive _ (hchar.trans hp)
      (hexp.trans hf) (by rw [hrank]; exact h))
  · exact Local81.of_hasWitness
      (CarrierTD.hasWitness_twShort _ (hchar.trans hp) (by rw [hrank]; exact h6))

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
