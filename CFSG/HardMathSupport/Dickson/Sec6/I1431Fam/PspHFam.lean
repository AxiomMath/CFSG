module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslFam

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne.Sec66T
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem y1431_noCfg_pspHighNe3 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hOut : OutDerived3At (fun t n p f => FamPspHigh t n p f ∧ p ≠ 3)) :
    Y1431NoCfgAt (fun t n p f => FamPspHigh t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn2, hn⟩, hp3⟩ := hF
  have hn3 : 3 ≤ n := by
    rcases hn with hn | hn
    · omega
    · exact absurd hn hp3
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) .PSp n p f hadm ht ⟨⟨rfl, hn2, hn⟩, hp3⟩ hm)
  have cS := c.descend e
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  refine s1431_false_psp hn3 hpk hO cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e (hin a' ha')

end CFSG.HardMathSupport.Dickson.Sec6.I1431
