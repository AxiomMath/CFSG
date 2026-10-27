module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslGood
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutHigh
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutPsu
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Sp4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem y1431_noCfg_pspHigh (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt FamPspHigh := by
  refine Y1431NoCfgAt.of_cover
    (Fam₁ := fun t n p f => FamPspHigh t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamPspHigh t n p f ∧ p = 3)
    (fun t n p f hF => ?_) (y1431_noCfg_pspHighNe3 hO outDerived3_pspHighNe3)
    (y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2) ?_)
  · by_cases hp : p = 3
    · exact Or.inr ⟨hF, hp⟩
    · exact Or.inl ⟨hF, hp⟩
  · rintro t n p f ⟨⟨rfl, -⟩, -⟩
    simp [CFSG.Blueprint.classicalTags]
  · rintro P _ _ t n p f hadm ht ⟨⟨rfl, hn2, -⟩, hp3⟩ hm
    have hC : StatedClassicalModel P .PSp n p f := (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    have hex : ¬ (n = 2 ∧ Nat.card K = 8) := by
      rintro ⟨-, h8⟩
      rw [hK, hp3] at h8
      have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hadm.2.1; omega)
      rw [h8] at h1
      omega
    exact famOK_of_mulEquiv e0 (famOK_psp hO hn2 hadm.1 hadm.2.1 hK hex)

theorem y1431_noCfg_psp (h0 : L2CentreThree)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (hKD : KDCharP 3) :
    Y1431NoCfgAt FamPsp :=
  y1431_psp_of_low h0 outDerived3_pspLow noE27_pspLow (y1431_noCfg_pspHigh hO hKD)

theorem y1431_noCfg_psuGoodHigh (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt FamPsuGoodHigh := by
  refine Y1431NoCfgAt.of_cover
    (Fam₁ := fun t n p f => FamPsuGoodHigh t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamPsuGoodHigh t n p f ∧ p = 3)
    (fun t n p f hF => ?_) (y1431_noCfg_psuGoodHighNe3 hO outDerived3_psuHighNe3)
    (y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2) ?_)
  · by_cases hp : p = 3
    · exact Or.inr ⟨hF, hp⟩
    · exact Or.inl ⟨hF, hp⟩
  · rintro t n p f ⟨⟨rfl, -⟩, -⟩
    simp [CFSG.Blueprint.classicalTags]
  · rintro P _ _ t n p f hadm ht ⟨⟨rfl, hn3, hdiv, -⟩, hp3⟩ hm
    have hC : StatedClassicalModel P .PSU n p f := (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨K, _, _, h, -, hq, ⟨e0⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hC
    haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      Finite.of_equiv P e0.toEquiv
    exact famOK_of_mulEquiv e0 (famOK_psu hO h hn3 hq hdiv)

theorem y1431_noCfg_psuGood (h0 : L2CentreThree)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (hKD : KDCharP 3) :
    Y1431NoCfgAt FamPsuGood :=
  y1431_psuGood_of_low h0 outDerived3_psuGoodThree noE27_psuGoodThree
    (y1431_noCfg_psuGoodHigh hO hKD)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
