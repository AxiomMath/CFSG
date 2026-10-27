module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

structure ParabolicParts : Prop where
  okT : enumOK 42 (wordTabs wT₀) (enumBFS 42 (wordTabs wT₀) 64) = true
  sizeT : (enumBFS 42 (wordTabs wT₀) 64).tabs.size = 64
  okB : enumOK 42 (wordTabs wB₀) (enumBFS 42 (wordTabs wB₀) 192) = true
  ok₁ : enumOK 42 (wordTabs wP₁) (enumBFS 42 (wordTabs wP₁) 960) = true
  size₁ : (enumBFS 42 (wordTabs wP₁) 960).tabs.size = 960
  ok₂ : enumOK 42 (wordTabs wP₂) (enumBFS 42 (wordTabs wP₂) 960) = true
  size₂ : (enumBFS 42 (wordTabs wP₂) 960).tabs.size = 960
  normal : normalOK 42 (enumBFS 42 (wordTabs wT₀) 64).tabs (wordTabs wB₀)
    ((wordTabs wB₀).map (invTab 42)) (wordTabs wT₀) = true
  inP : ∀ j < (wordTabs wB₀).size,
    found (indexOf (enumBFS 42 (wordTabs wP₁) 960).tabs) (enumBFS 42 (wordTabs wP₁) 960).tabs
      (wordTabs wB₀)[j]! = true ∧
    found (indexOf (enumBFS 42 (wordTabs wP₂) 960).tabs) (enumBFS 42 (wordTabs wP₂) 960).tabs
      (wordTabs wB₀)[j]! = true
  invs : invsOK 42 (wordTabs wReps) ((wordTabs wReps).map (invTab 42)) = true
  cosets : ∀ i < (enumBFS 42 gensS 20160).tabs.size, ∃ k < (wordTabs wReps).size,
    found (indexOf (enumBFS 42 (wordTabs wB₀) 192).tabs) (enumBFS 42 (wordTabs wB₀) 192).tabs
      (comp 42 ((wordTabs wReps).map (invTab 42))[k]! (enumBFS 42 gensS 20160).tabs[i]!) = true
  reps : ∀ k < wReps.length,
    wordPerm (wReps.getD k []) ∈ Subgroup.closure (wordSet wP₁) ∨
      wordPerm (wReps.getD k []) ∈ Subgroup.closure (wordSet wP₂) ∨
      Subgroup.closure (wordSet (wB₀ ++ [wReps.getD k []])) = S

end CFSG.ComponentClassification.GrSLit.L34Facts
