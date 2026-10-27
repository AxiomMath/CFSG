module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def normT0OK (ES : Array Tab) : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  let EB := enumBFS 42 (wordTabs wB₀) 192
  EB.tabs.size == 192 &&
    allBelow ES.size fun i =>
      invOK ES[i]! &&
        (found (indexOf EB.tabs) EB.tabs ES[i]! ||
          anyBelow (wordTabs wT₀).size fun j =>
            notInOK ET.tabs (conjTab 42 ES[i]! (invTab 42 ES[i]!) (wordTabs wT₀)[j]!))

@[expose] def centerT0OK : Bool :=
  allBelow 64 fun k =>
    (allBelow (wordTabs wT₀).size fun j =>
      comp 42 (tgT k) (wordTabs wT₀)[j]! == comp 42 (wordTabs wT₀)[j]! (tgT k)) ==
      [0, 4, 8, 12].contains k

@[expose] def wU₁ : List (List ℕ) := [tg 1, tg 2, tg 4, tg 8]

@[expose] def wU₂ : List (List ℕ) := [tg 4, tg 8, tg 16, tg 32]

@[expose] def parabolicUOK : Bool :=
  let E₁ := enumBFS 42 (wordTabs wU₁) 16
  let E₂ := enumBFS 42 (wordTabs wU₂) 16
  let E₁₂ := enumBFS 42 (wordTabs (wP₁ ++ wP₂)) 20160
  enumOK 42 (wordTabs wU₁) E₁ && E₁.tabs.size == 16 &&
    enumOK 42 (wordTabs wU₂) E₂ && E₂.tabs.size == 16 &&
    (allBelow 16 fun k => found (indexOf E₁.tabs) E₁.tabs (tgT k)) &&
    (allBelow 16 fun k => found (indexOf E₂.tabs) E₂.tabs (tgT (4 * k))) &&
    normalOK 42 E₁.tabs (wordTabs wP₁) ((wordTabs wP₁).map (invTab 42)) (wordTabs wU₁) &&
    normalOK 42 E₂.tabs (wordTabs wP₂) ((wordTabs wP₂).map (invTab 42)) (wordTabs wU₂) &&
    enumOK 42 (wordTabs (wP₁ ++ wP₂)) E₁₂ && E₁₂.tabs.size == 20160

@[expose] def prodData : List (ℕ × ℕ × ℕ) := [(4, 8, 12), (1, 2, 3)]

@[expose] def prodOK : Bool :=
  prodData.all fun d => comp 42 (tgT d.1) (tgT d.2.1) == tgT d.2.2

@[noinline, expose] def sylowOK (ES : Array Tab) : Bool :=
  normT0OK ES && centerT0OK && parabolicUOK && prodOK

end CFSG.ComponentClassification.GrSLit.L34Facts
