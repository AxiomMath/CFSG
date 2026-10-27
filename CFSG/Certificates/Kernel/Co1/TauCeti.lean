module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One
public import CFSG.Certificates.Kernel.Co1.Data.Co1B

public section

namespace CFSG.KC.Co1Top

@[expose] def lceEntry (w : List (ℕ × Bool)) : ℕ :=
  4 * w.length + 4096 * w.foldr (fun l acc => (2 * l.1 + if l.2 then 0 else 1) + 256 * acc) 0

theorem top_eq :
    TauCeti.Sporadic.co1Presentation.relatorLetters.map lceEntry =
      (List.range 45).map CFSG.KD.Co1B.TOPT := by
  rw [TauCeti.Sporadic.co1Presentation_relatorLetters]
  decide +kernel

end CFSG.KC.Co1Top

end
