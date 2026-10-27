module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27L3U3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Descent

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

theorem famOK_of_mulEquiv {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P']
    (e : P ≃* P') (h : FamOK P') : FamOK P := by
  intro ψ hψ3 hninn
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hninn' : ¬ IsInnerAut (MulAut.congr e ψ) := fun hinn =>
    hninn ((isInnerAut_congr e ψ).1 hinn)
  obtain ⟨γ', f', hγ', hf'⟩ := h _ hψ3' hninn'
  have hback : ∀ φ : MulAut P, MulAut.congr e.symm (MulAut.congr e φ) = φ := fun φ => by
    ext x
    simp [MulAut.congr]
  refine ⟨MulAut.congr e.symm γ', MulAut.congr e.symm f', ?_, ?_⟩
  · have := congrArg (MulAut.congr e.symm) hγ'
    rw [hback, map_mul, map_mul, map_inv] at this
    exact this
  · intro A hA r hr hT
    let π : P →* P' := (e : P →* P')
    have hπ : Function.Surjective π := e.surjective
    have hker : π.ker ≤ Subgroup.center P := by
      intro x hx
      have : x = 1 := e.injective (by simpa [π] using hx)
      rw [this]
      exact one_mem _
    have hαψ : ∀ y, π ((MulAut.congr e.symm f') y) = f' (π y) := fun y => by
      simp [π, MulAut.congr]
    obtain ⟨A', hA', hT'⟩ := typeL2_barOf_of_central π hπ hker (MulAut.congr e.symm f') f' hαψ hA hT
    exact hf' A' hA' r hr hT'

theorem y1431_noCfg_pslGoodHigh_three (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt (fun t n p f => FamPslGoodHigh t n p f ∧ p = 3) := by
  refine y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2) ?_
  · rintro t n p f ⟨⟨rfl, -⟩, -⟩
    simp [CFSG.Blueprint.classicalTags]
  · rintro P _ _ t n p f hadm ht ⟨⟨rfl, hn3, hcop, -⟩, hp3⟩ hm
    have hC : StatedClassicalModel P .PSL n p f := (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    have hcopK : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1)) := by rw [hK]; exact hcop
    haveI : Finite (projectiveSL n K) := inferInstance
    exact famOK_of_mulEquiv (e0.trans (statedProjEquiv n K))
      (famOK_psl hO hn3 hcopK hadm.1 hadm.2.1 hK)

theorem y1431_noCfg_pslGood (h0 : L2CentreThree)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (hKD : KDCharP 3) :
    Y1431NoCfgAt FamPslGood := by
  refine y1431_pslGood_of_low h0 noE27_pslGoodThree ?_
  refine Y1431NoCfgAt.of_cover (Fam₁ := fun t n p f => FamPslGoodHigh t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamPslGoodHigh t n p f ∧ p = 3) (fun t n p f hF => ?_)
    (y1431_noCfg_pslGoodHigh_ne3 hO) (y1431_noCfg_pslGoodHigh_three hO hKD)
  by_cases hp : p = 3
  · exact Or.inr ⟨hF, hp⟩
  · exact Or.inl ⟨hF, hp⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
