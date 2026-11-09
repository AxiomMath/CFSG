module

public import Init

public section

namespace CFSG.EvenSporadicStandard.Fin76b

@[expose] def fstR {α β : Type} (p : α × β) : α := p.1

theorem fstR_eq {α β : Type} (p : α × β) : fstR p = p.1 := rfl

end CFSG.EvenSporadicStandard.Fin76b

end
