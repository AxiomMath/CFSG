module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResUntw
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTwE6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResChar3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutE
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutTwE6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResKac
public import CFSG.HardMathSupport.Dickson.KD.CharP
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section All


theorem excres_char3_noField {P : Type} [Group P] [Finite P] {t : StatedLieTag} {n f : ℕ}
    (ht : t ≠ .PSL ∧ t ≠ .PSp) (hm : CFSG.Blueprint.LieModel P t n 3 f) {x : P} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) {J : Subgroup P} (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J) :
    False :=
  excres_false_of_char3 (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds Nat.prime_three
    (by norm_num)) CFSG.TauCetiBridge.typewiseBridges (excres_not_tauCetiDuplicate ht n 3 f) hm
    hx1 hx3 hJ

theorem excInnerNoField_f4 (hTLin : ExcTLInner Tag.F4) (hTLin2 : ExcTLInnerTwo Tag.F4)
    (hTLout : ExcTLOther Tag.F4) : ExcInnerNoField FamF4 := by
  intro P _ _ t n p f hadm ht hF hm x y hx1 hx3 hy3 hxy J q hJ hq hq3 hq8 hq10
  obtain rfl := hF
  by_cases hp3 : p = 3
  · subst hp3
    exact fun _ => excres_char3_noField (by decide) hm hx1 hx3 hJ
  · have hU : UntwistedChevalleyModel P .F4 (p ^ f) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact excres_noField_untw (Or.inl rfl) excKac_f4 hTLin hTLin2 hTLout hadm.1
      hadm.2.1 hp3 hU hx1 hx3 hy3 hJ hq hq3 hq8 hq10

theorem excInnerNoField_e7 (hTLin : ExcTLInner Tag.E7) (hTLin2 : ExcTLInnerTwo Tag.E7)
    (hTLout : ExcTLOther Tag.E7) : ExcInnerNoField FamE7 := by
  intro P _ _ t n p f hadm ht hF hm x y hx1 hx3 hy3 hxy J q hJ hq hq3 hq8 hq10
  obtain rfl := hF
  by_cases hp3 : p = 3
  · subst hp3
    exact fun _ => excres_char3_noField (by decide) hm hx1 hx3 hJ
  · have hU : UntwistedChevalleyModel P .E7 (p ^ f) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact excres_noField_untw (Or.inr (Or.inr (Or.inl rfl))) excKac_e7 hTLin hTLin2 hTLout hadm.1
      hadm.2.1 hp3 hU hx1 hx3 hy3 hJ hq hq3 hq8 hq10

theorem excInnerNoField_e8 (hTLin : ExcTLInner Tag.E8) (hTLin2 : ExcTLInnerTwo Tag.E8)
    (hTLout : ExcTLOther Tag.E8) : ExcInnerNoField FamE8 := by
  intro P _ _ t n p f hadm ht hF hm x y hx1 hx3 hy3 hxy J q hJ hq hq3 hq8 hq10
  obtain rfl := hF
  by_cases hp3 : p = 3
  · subst hp3
    exact fun _ => excres_char3_noField (by decide) hm hx1 hx3 hJ
  · have hU : UntwistedChevalleyModel P .E8 (p ^ f) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact excres_noField_untw (Or.inr (Or.inr (Or.inr rfl))) excKac_e8 hTLin hTLin2 hTLout hadm.1
      hadm.2.1 hp3 hU hx1 hx3 hy3 hJ hq hq3 hq8 hq10

theorem excInnerNoField_e6Good (hTLin : ExcTLInner Tag.E6) (hTLin2 : ExcTLInnerTwo Tag.E6)
    (hTLout : ExcTLOther Tag.E6) : ExcInnerNoField FamE6Good := by
  intro P _ _ t n p f hadm ht hF hm x y hx1 hx3 hy3 hxy J q hJ hq hq3 hq8 hq10
  obtain ⟨rfl, -⟩ := hF
  by_cases hp3 : p = 3
  · subst hp3
    exact fun _ => excres_char3_noField (by decide) hm hx1 hx3 hJ
  · have hU : UntwistedChevalleyModel P .E6 (p ^ f) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact excres_noField_untw (Or.inr (Or.inl rfl)) excKac_e6 hTLin hTLin2 hTLout hadm.1
      hadm.2.1 hp3 hU hx1 hx3 hy3 hJ hq hq3 hq8 hq10

theorem excInnerNoField_twE6Good (hTLin : ExcTLInner Tag.E6) (hTLin2 : ExcTLInnerTwo Tag.E6)
    (hTLout : ExcTLOther Tag.E6) : ExcInnerNoField FamTwE6Good := by
  intro P _ _ t n p f hadm ht hF hm x y hx1 hx3 hy3 hxy J q hJ hq hq3 hq8 hq10
  obtain ⟨rfl, -⟩ := hF
  by_cases hp3 : p = 3
  · subst hp3
    exact fun _ => excres_char3_noField (by decide) hm hx1 hx3 hJ
  · have hE : TwistedChevalleyModel P TwistTag.E6 (p ^ f) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact excres_noField_twE6 excKac_e6 hTLin hTLin2 hTLout hadm.1 hadm.2.1 hp3 hE hx1 hx3 hy3 hJ
      hq hq3 hq8 hq10

theorem excResidual_f4 (hTLin : ExcTLInner Tag.F4) (hTLin2 : ExcTLInnerTwo Tag.F4)
    (hTLout : ExcTLOther Tag.F4) : ExcResidual FamF4 :=
  ⟨outDerived3_f4, excInnerNoField_f4 hTLin hTLin2 hTLout⟩

theorem excResidual_e6Good (hTLin : ExcTLInner Tag.E6) (hTLin2 : ExcTLInnerTwo Tag.E6)
    (hTLout : ExcTLOther Tag.E6) : ExcResidual FamE6Good :=
  ⟨outDerived3_e6Good, excInnerNoField_e6Good hTLin hTLin2 hTLout⟩

theorem excResidual_twE6Good (hTLin : ExcTLInner Tag.E6) (hTLin2 : ExcTLInnerTwo Tag.E6)
    (hTLout : ExcTLOther Tag.E6) : ExcResidual FamTwE6Good :=
  ⟨outDerived3_twE6Good, excInnerNoField_twE6Good hTLin hTLin2 hTLout⟩

theorem excResidual_e7 (hTLin : ExcTLInner Tag.E7) (hTLin2 : ExcTLInnerTwo Tag.E7)
    (hTLout : ExcTLOther Tag.E7) : ExcResidual FamE7 :=
  ⟨outDerived3_e7, excInnerNoField_e7 hTLin hTLin2 hTLout⟩

theorem excResidual_e8 (hTLin : ExcTLInner Tag.E8) (hTLin2 : ExcTLInnerTwo Tag.E8)
    (hTLout : ExcTLOther Tag.E8) : ExcResidual FamE8 :=
  ⟨outDerived3_e8, excInnerNoField_e8 hTLin hTLin2 hTLout⟩

end All

end CFSG.HardMathSupport.Dickson.Sec6.I1431
