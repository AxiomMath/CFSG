module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def uWordsPlus : List (List ℤ) := [[3], [9, 5], [5], [10, 7], [11], [7]]

@[expose] def utArr (k : ℕ) : Array ℕ := OmegaEight.omegaW (uWordsPlus.getD k [])

@[expose] def rho2Arr : Array ℕ := compA 360 OmegaEight.genArrs[8]! OmegaEight.genArrs[8]!

@[expose] def sigArr (lift : Array ℕ) : Array ℕ :=
  OmegaEight.copy0Arr (conjA 360 rho2Arr lift)

@[expose] def sigTarget : ℕ → Array ℕ
  | 0 => psiArr .plus 1
  | 1 => psiArr .plus 2
  | 2 => uArr .plus 3
  | 3 => psiArr .plus 4
  | 4 => uArr .plus 4
  | 5 => uArr .plus 5
  | _ => #[]

@[expose] def stabB (s : Array ℕ) (M : Array Bool) : Bool :=
  allLt 120 fun z => !(M.getD z false) || M.getD s[z]! false

@[expose] def flagA : Array Bool :=
  Array.ofFn (n := 120) fun z => [1, 2].all fun s => !OmegaEight.bNat OmegaEight.nsArr[z.val]! s

@[expose] def flagB : Array Bool :=
  Array.ofFn (n := 120) fun z => [1, 2, 4].all fun s => !OmegaEight.bNat OmegaEight.nsArr[z.val]! s

@[expose] def fmask (A : Array Bool) (g : Array ℕ) : Array Bool :=
  Array.ofFn (n := 120) fun z => A.getD (invCand 120 g)[z.val]! false

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
