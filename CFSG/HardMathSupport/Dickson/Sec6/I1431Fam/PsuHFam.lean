module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslFam
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem y1431_noCfg_psuGoodHighNe3 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hOut : OutDerived3At (fun t n p f => FamPsuGoodHigh t n p f ∧ p ≠ 3)) :
    Y1431NoCfgAt (fun t n p f => FamPsuGoodHigh t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hdiv, hn'⟩, hp3⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  haveI : Finite (primeFormP h (idGram K n)) := inferInstance
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) .PSU n p f hadm ht ⟨⟨rfl, hn3, hdiv, hn'⟩, hp3⟩ hm)
  have cS := c.descend e0
  have hnq : ¬ (n = 3 ∧ p ^ f = 2) := fun hc => by
    rcases hn' with hn'' | hn''
    · exact hn'' hc.1
    · exact hp3 hn''
  refine s1431_false_psu hO h hn3 hnq hp3 hdiv cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e0 (hin a' ha')

end CFSG.HardMathSupport.Dickson.Sec6.I1431
