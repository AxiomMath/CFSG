module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native

@[expose] def wT₀ : List (List ℕ) :=
  [[0, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 2, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 1, 0, 0],
    [0, 1, 0, 2, 0, 0, 1, 0, 0]]

@[expose] def wB₀ : List (List ℕ) :=
  [[0, 0, 1, 0, 1, 0, 1], [2, 0, 0, 1, 0, 1, 0, 2], [0, 1, 0, 0, 1, 0, 1, 0, 0]]

@[expose] def wP₁ : List (List ℕ) := [[1, 0, 1], [0, 0, 1, 0], [0, 0, 2, 0]]

@[expose] def wP₂ : List (List ℕ) := [[1], [2], [0, 0, 1, 0, 1, 0]]

@[expose] def wReps : List (List ℕ) :=
    [[], [0], [1], [2], [0, 0], [1, 0], [2, 0], [0, 1], [2, 1], [0, 2], [1, 0, 0], [2, 0, 0],
     [0, 1, 0], [2, 1, 0], [0, 2, 0], [0, 0, 1], [1, 0, 1], [2, 0, 1], [0, 2, 1], [0, 0, 2],
     [1, 0, 2], [2, 0, 2], [0, 1, 0, 0], [2, 1, 0, 0], [0, 2, 0, 0], [1, 0, 1, 0], [2, 0, 1, 0],
     [0, 2, 1, 0], [0, 0, 2, 0], [1, 0, 2, 0], [2, 0, 2, 0], [1, 0, 0, 1], [2, 0, 0, 1],
     [2, 1, 0, 1], [0, 2, 0, 1], [0, 0, 2, 1], [1, 0, 2, 1], [2, 0, 2, 1], [1, 0, 0, 2],
     [2, 0, 0, 2], [2, 1, 0, 2], [0, 2, 0, 2], [0, 0, 1, 0, 0], [0, 2, 1, 0, 0], [0, 0, 2, 0, 0],
     [1, 0, 2, 0, 0], [2, 0, 2, 0, 0], [0, 1, 0, 1, 0], [2, 1, 0, 1, 0], [0, 2, 0, 1, 0],
     [0, 0, 2, 1, 0], [1, 0, 2, 1, 0], [2, 0, 2, 1, 0], [1, 0, 0, 2, 0], [2, 0, 0, 2, 0],
     [0, 1, 0, 2, 0], [2, 1, 0, 2, 0], [0, 2, 0, 2, 0], [0, 1, 0, 0, 1], [2, 1, 0, 0, 1],
     [0, 2, 1, 0, 1], [0, 0, 2, 0, 1], [1, 0, 2, 0, 1], [1, 0, 0, 2, 1], [2, 0, 0, 2, 1],
     [2, 1, 0, 2, 1], [0, 2, 0, 2, 1], [0, 1, 0, 0, 2], [2, 1, 0, 0, 2], [0, 2, 0, 0, 2],
     [0, 2, 1, 0, 2], [0, 0, 2, 0, 2], [1, 0, 2, 0, 2], [2, 0, 2, 0, 2], [0, 0, 2, 1, 0, 0],
     [1, 0, 2, 1, 0, 0], [2, 0, 2, 1, 0, 0], [2, 0, 0, 2, 0, 0], [0, 2, 0, 2, 0, 0],
     [0, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0], [0, 2, 1, 0, 1, 0], [1, 0, 2, 0, 1, 0],
     [0, 1, 0, 2, 1, 0], [2, 1, 0, 2, 1, 0], [2, 1, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0],
     [0, 0, 1, 0, 2, 0], [0, 0, 2, 0, 2, 0], [1, 0, 2, 0, 2, 0], [0, 0, 1, 0, 0, 1],
     [0, 2, 1, 0, 0, 1], [1, 0, 2, 1, 0, 1], [1, 0, 0, 2, 0, 1], [0, 1, 0, 0, 2, 1],
     [2, 1, 0, 0, 2, 1], [0, 0, 1, 0, 0, 2], [2, 0, 2, 1, 0, 2], [1, 0, 0, 2, 0, 2],
     [2, 0, 0, 2, 1, 0, 0], [0, 1, 0, 1, 0, 1, 0], [2, 0, 2, 1, 0, 1, 0], [0, 0, 1, 0, 2, 1, 0],
     [1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 2, 1]]

@[noinline, expose] def parabolicOK (ES : Array Tab) : Bool :=
  let gT := wordTabs wT₀
  let gB := wordTabs wB₀
  let g₁ := wordTabs wP₁
  let g₂ := wordTabs wP₂
  let ET := enumBFS 42 gT 64
  let EB := enumBFS 42 gB 192
  let E₁ := enumBFS 42 g₁ 960
  let E₂ := enumBFS 42 g₂ 960
  let iB := indexOf EB.tabs
  let i₁ := indexOf E₁.tabs
  let i₂ := indexOf E₂.tabs
  let reps := wordTabs wReps
  let ri := reps.map (invTab 42)
  (enumOK 42 gT ET && ET.tabs.size == 64) && enumOK 42 gB EB &&
    (enumOK 42 g₁ E₁ && E₁.tabs.size == 960) && (enumOK 42 g₂ E₂ && E₂.tabs.size == 960) &&
    normalOK 42 ET.tabs gB (gB.map (invTab 42)) gT &&
    (allBelow gB.size fun j => found i₁ E₁.tabs gB[j]! && found i₂ E₂.tabs gB[j]!) &&
    invsOK 42 reps ri &&
    (allBelow ES.size fun i =>
      anyBelow reps.size fun k => found iB EB.tabs (comp 42 ri[k]! ES[i]!)) &&
    allBelow wReps.length fun k =>
      found i₁ E₁.tabs reps[k]! || found i₂ E₂.tabs reps[k]! ||
        (let gs := wordTabs (wB₀ ++ [wReps.getD k []])
         let E := enumBFS 42 gs 20160
         enumOK 42 gs E && E.tabs.size == 20160)

end CFSG.ComponentClassification.GrSLit.L34Facts
