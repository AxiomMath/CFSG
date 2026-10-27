module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreKerDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.GroupActions
open scoped Pointwise


theorem e6ToralComponentAction_of_kernel (hK : ExcKernelCompAction)
    (hLang : E6ToralLangSetup) (hExit : E6ToralKernelExit)
    (h360 : E6ToralLangSetupH360) : E6ToralComponentAction := by
  intro n K _ _ _ hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm
  obtain ⟨D⟩ := hLang n K hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm
    (h360 n K hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm)
  have hinn := hK (τ := Tag.E6) (L := AlgebraicClosure K) D.S (by norm_num) (by norm_num)
    (p := 3) (by norm_num) (by norm_num)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) D.hT D.hap D.hpow D.h1
    (fun h => by cases h) D.i D.hQS D.h360 D.hyZ D.hyF D.hyStab
  exact hExit n K hn hKcard h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus Kc hKc hnorm D hinn

theorem twE6W0ToralComponentAction_of_kernel (hK : ExcKernelCompAction)
    (hLang : TwE6ToralLangSetup) (hExit : TwE6ToralKernelExit)
    (h360 : TwE6ToralLangSetupH360) : TwE6W0ToralComponentAction := by
  intro n K _ _ hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus Kc hKc hnorm
  haveI hcharK : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by
    rw [hKcard, pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨D⟩ := hLang n K hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg
    hn0 htorus Kc hKc hnorm
    (h360 n K hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus Kc hKc hnorm)
  have hinn := hK (τ := Tag.E6) (L := AlgebraicClosure K) D.S (by norm_num) (by norm_num)
    (p := 3) (by norm_num) (by norm_num)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) D.hT D.hap D.hpow D.h1
    (fun h => by cases h) D.i D.hQS D.h360 D.hyZ D.hyF D.hyStab
  exact hExit n K hn hKcard h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg
    hn0 htorus Kc hKc hnorm D hinn

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
