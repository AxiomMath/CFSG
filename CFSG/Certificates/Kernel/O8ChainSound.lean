module

public import CFSG.Certificates.Kernel.O8ChainDefs
import CFSG.Certificates.Kernel.O8S0Proved
public import Certificates.Data.Kernel.O8.S0

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT

theorem s0_sound {S : Array (Array ℕ)} {U : ℕ → Array ℕ} {tr : Array (ℕ × ℕ)}
    {L MT UP UI TR : Nat} (hL : S0Bind S L) (hU : ∀ k < 6, U k = decR (mat UP k))
    (hT : ∀ i < 64, tr.getD i (0, 0) = (fget TR i 9 % 8, fget TR i 9 / 8))
    (hm : mtOK L MT = true) (h : s0OK L MT UP UI TR = true) : s0CheckG S U tr = true :=
  s0_sound_proved hL hU hT hm h

theorem abel_sound {S : Array (Array ℕ)} {ms : List ℕ} {L MT F AM n CI : Nat} (hL : S0Bind S L)
    (hA : ms = (List.range n).map fun k => fget AM k 64) (hn : 0 < n)
    (hd : distinctOK L = true) (hm : mtOK L MT = true) (h : abelOK L MT F AM n CI = true) :
    abelCheckG S ms = true :=
  abel_sound_proved hL hA hn hd hm h

end CFSG.KC.O8

end
