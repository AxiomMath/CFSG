module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

@[expose] def cosXor (a b : Fin 4) : Fin 4 :=
  ⟨a.val ^^^ b.val, by have := Nat.xor_lt_two_pow (n := 2) a.isLt b.isLt; omega⟩

@[expose] def qmulC (c d : Fin 4 × Fin 4 × Bool) : Fin 4 × Fin 4 × Bool :=
  if d.2.2 then (cosXor c.2.1 d.1, cosXor c.1 d.2.1, xor c.2.2 d.2.2)
  else (cosXor c.1 d.1, cosXor c.2.1 d.2.1, xor c.2.2 d.2.2)

end CFSG.ComponentClassification.GrSLit.L34Tw
