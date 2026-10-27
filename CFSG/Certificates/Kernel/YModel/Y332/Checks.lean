module

public import CFSG.Certificates.Kernel.YModel.Y332.Data
public import CFSG.YGroups.Defs
public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
import CFSG.Certificates.Kernel.Common.Each
public import Mathlib

public section

set_option maxRecDepth 100000

namespace CFSG.KD.YMY332

open CFSG.KC.YModel CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier

#kc_each letChk 0 9

@[expose] noncomputable def comChk (c : Nat) : Bool := weqK 15 9 Nf (f332Word ++ [c]) ([c] ++ f332Word)

#kc_each comChk 0 9

theorem w_spider :
    weqK 15 9 Nf (List.replicate 3 ((List.replicate 5 (spiderWord 3 3)).flatten ++ [0])).flatten [] =
      true := by
  quickRfl

theorem w_conj : weqK 15 9 Nf (y332Conj.reverse ++ [0, 3, 8] ++ y332Conj) ([3, 4, 6, 8] ++ f332Word) =
    true := by
  quickRfl

theorem w_fne : (!weqK 15 9 Nf f332Word []) = true := by
  quickRfl

theorem w_fsq : weqK 15 9 Nf (f332Word ++ f332Word) [] = true := by
  quickRfl

theorem neg :
    (!weqK 15 9 Nf [0] [] &&
      !weqK 15 9 Nf (y332Conj.reverse ++ [0, 3, 8] ++ y332Conj.dropLast) ([3, 4, 6, 8] ++ f332Word) &&
      !weqK 15 9 Nf (f332Word.dropLast ++ [5]) ([5] ++ f332Word.dropLast)) = true := by
  quickRfl

end CFSG.KD.YMY332

end
