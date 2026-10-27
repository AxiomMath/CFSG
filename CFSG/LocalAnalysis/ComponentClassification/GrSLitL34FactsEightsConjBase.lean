
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsCertInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

structure ConjParts : Prop where
  p1 : ∀ d ∈ conjP1Data, found (indexOf (enumBFS 42 (wordTabs wP₁) 960).tabs)
    (enumBFS 42 (wordTabs wP₁) 960).tabs (wordTab d.2) = true ∧ invOK (wordTab d.2) = true ∧
    conjTab 42 (wordTab d.2) (invTab 42 (wordTab d.2)) (tgT d.1) = tgT 4
  p2 : ∀ d ∈ conjP2Data, found (indexOf (enumBFS 42 (wordTabs wP₂) 960).tabs)
    (enumBFS 42 (wordTabs wP₂) 960).tabs (wordTab d.2) = true ∧ invOK (wordTab d.2) = true ∧
    conjTab 42 (wordTab d.2) (invTab 42 (wordTab d.2)) (tgT (4 * d.1)) = tgT 4

private theorem conjP1_idx : ∀ k < 16, k ≠ 0 → ∃ d ∈ conjP1Data, d.1 = k := by decide

private theorem conjP2_idx : ∀ k < 16, k ≠ 0 → ∃ d ∈ conjP2Data, d.1 = k := by decide

end CFSG.ComponentClassification.GrSLit.L34Facts
