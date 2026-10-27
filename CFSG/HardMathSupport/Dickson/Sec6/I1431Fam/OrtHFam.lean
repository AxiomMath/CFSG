module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHOut
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslFam
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem y1431_noCfg_orthOddNe3 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hOut : OutDerived3At (fun t n p f => FamOrthOdd t n p f ∧ p ≠ 3)) :
    Y1431NoCfgAt (fun t n p f => FamOrthOdd t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨hFt, hp3⟩ := hF
  subst hFt
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaOdd n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) .POmegaOdd n p f hadm ht ⟨rfl, hp3⟩ hm)
  have hring : ringChar K = p := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two (by rw [hring]; exact hadm.1), hring]
    exact hadm.2.2.2
  obtain ⟨hQ, hT⟩ := regular_quadOdd (K := K) (n := n) h2 hadm.2.2.1
  let e' : (Y ⧸ Subgroup.center Y) ≃* ProjOrthDerived (quadOdd n K) :=
    e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadOdd n K))
  have cS := c.descend e'
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  refine s1431_false_orth hO hQ hT hpk cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e' (hin a' ha')

theorem y1431_noCfg_orthPlusNe3 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hOut : OutDerived3At (fun t n p f => FamOrthPlus t n p f ∧ p ≠ 3)) :
    Y1431NoCfgAt (fun t n p f => FamOrthPlus t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨hFt, hn5⟩, hp3⟩ := hF
  subst hFt
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) .POmegaPlus n p f hadm ht ⟨⟨rfl, hn5⟩, hp3⟩ hm)
  obtain ⟨hQ, hT⟩ := regular_quadPlus (K := K) (n := n) (by omega)
  let e' : (Y ⧸ Subgroup.center Y) ≃* ProjOrthDerived (quadPlus n K) :=
    e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadPlus (n := n) (K := K)))
  have cS := c.descend e'
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  refine s1431_false_orth hO hQ hT hpk cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e' (hin a' ha')

theorem y1431_noCfg_orthMinusNe3 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hOut : OutDerived3At (fun t n p f => FamOrthMinus t n p f ∧ p ≠ 3)) :
    Y1431NoCfgAt (fun t n p f => FamOrthMinus t n p f ∧ p ≠ 3) := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨hFt, hp3⟩ := hF
  subst hFt
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, b, cc, hirr, ⟨e⟩⟩ := hC
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) .POmegaMinus n p f hadm ht ⟨rfl, hp3⟩ hm)
  obtain ⟨hQ, hT⟩ := regular_quadMinus (K := K) (n := n) hadm.2.2 hirr
  let e' : (Y ⧸ Subgroup.center Y) ≃* ProjOrthDerived (quadMinus n K b cc) :=
    e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadMinus n K b cc))
  have cS := c.descend e'
  have hpk : (3 : K) ≠ 0 := CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hadm.1 hp3 hK
  refine s1431_false_orth hO hQ hT hpk cS (ten_le_of_cube hq0 hqq) ?_
  rintro a ⟨a', ha', rfl⟩
  exact descendHom_isInnerAut e' (hin a' ha')

theorem y1431_noCfg_orthOddNe3' (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt (fun t n p f => FamOrthOdd t n p f ∧ p ≠ 3) :=
  y1431_noCfg_orthOddNe3 hO outDerived3_orthOddNe3

theorem y1431_noCfg_orthPlusNe3' (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt (fun t n p f => FamOrthPlus t n p f ∧ p ≠ 3) :=
  y1431_noCfg_orthPlusNe3 hO outDerived3_orthPlusNe3

theorem y1431_noCfg_orthMinusNe3' (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt (fun t n p f => FamOrthMinus t n p f ∧ p ≠ 3) :=
  y1431_noCfg_orthMinusNe3 hO outDerived3_orthMinusNe3

end CFSG.HardMathSupport.Dickson.Sec6.I1431
