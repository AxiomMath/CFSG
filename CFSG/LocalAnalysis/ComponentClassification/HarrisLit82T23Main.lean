module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Three
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem harris82Theorem2SLTwo_of_theorem1 (hT1 : Harris82Theorem1KProper)
    (hGA : TBLit.GriessMultipliersAllModels) (hID : Harris81Lemma35IdentFact) :
    Harris82Theorem2SLTwo :=
  T23.harris82Theorem2SLTwo_holds hT1 hGA hID

theorem harris82Theorem3SLTwo_of_theorem1
    (hT1 : Harris82Theorem1KProper) (hGA : TBLit.GriessMultipliersAllModels)
    (hID : Harris81Lemma35IdentFact) (hCI : GSLit.ClassicalInvolutionInput) :
    Harris82Theorem3SLTwo :=
  T23.harris82Theorem3SLTwo_of hCI hGA (harris82Theorem2SLTwo_of_theorem1 hT1 hGA hID)

namespace L35

theorem statement_holds_slTwo (hT1 : Harris82Theorem1KProper) (hT3 : Harris82Theorem3SLTwo)
    (hID : Harris81Lemma35IdentFact) : Harris81Lemma35Step := by
  intro G _ _ _ hnonab hK hcat p hp hp2 W hW2 hW4 L hL hM k hk hs5 hLsl hLW w hw hw1 v hv hvw K
    hKdef
  obtain ⟨hwL, hwW⟩ := mem_inf.mp hw
  obtain ⟨hw2, hv2, hvM, hCW⟩ := centralizer_eq_inf hW2 hW4 hwW hw1 hv hvw
  have hL' : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v}) := by
    rw [← hCW]
    exact hL
  have hLv : L ≤ centralizer {v} := hL'.1.trans inf_le_right
  have hKcomm : K = ⁅L, GSThmB.layerIn (centralizer {w})⁆ := by
    rw [hKdef]
    exact conjClosure_eq_commutator hv2 hvM hL'
  have hKv : K.map (MulAut.conj v).toMonoidHom = K := by
    rw [hKcomm]
    exact map_conj_commutator_eq hvM hLv
  have hKc : IsTwoComponentIn K (centralizer {w}) := by
    rw [hKdef]
    exact hT3 G hnonab hK hcat W hW2 hW4 L p hp hp2 hL hM k hk hs5 hLsl w hw hw1
  have hLK : L ≤ K := by
    rw [hKdef]
    exact GSThmB.B5a.le_conjClosure L _
  have hwK : w ∈ K := hLK hwL
  have hKM : ¬ IsMTypeSchur p ↥K :=
    not_isMTypeSchur_of_kProper hT1 hnonab hK hcat hw2 hKc hwK hp hp2
  obtain ⟨hLeq, hcases⟩ := hID G hnonab hK hcat p hp hp2 w v hw2 (hW2 v hv) hvw hvM L hL' hM k hk
    hs5 hLsl hwL K hKdef hLK hKc hwK hKM hKv
  exact ⟨hwK, hKcomm, hKc, hKv, hLeq, hcases⟩

end L35

end CFSG.ComponentClassification.HarrisLit
