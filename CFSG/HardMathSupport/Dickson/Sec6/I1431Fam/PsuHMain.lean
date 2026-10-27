module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHShell
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHKey

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.RankThree.PartTwo.KFacts

theorem s1431_false_psu (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hnq : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hℓ3 : ℓ ≠ 3) (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1))
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} {ψ : MulAut (primeFormP h (idGram K n))}
    {J : Subgroup (primeFormP h (idGram K n))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K n)) A ψ J q) (hq : 10 ≤ q)
    (hA : ∀ a ∈ A, IsInnerAut a) : False :=
  s1431_false_psu_of_key h hn hnq hℓ3 hdiv c hA fun a ha3 i hT =>
    psuBlock_key hO hℓ3 a ha3 i hq hT

end CFSG.HardMathSupport.Dickson.Sec6.I1431
