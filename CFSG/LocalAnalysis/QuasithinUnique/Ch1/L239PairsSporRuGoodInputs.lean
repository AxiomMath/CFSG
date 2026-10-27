module

public import CFSG.Sporadic.Schreier.RuArrays

public noncomputable section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruWC (w : List ℤ) : Array ℕ :=
  wordA 4060 #[ruC0A, ruC1A] #[ruInv ruC0A, ruInv ruC1A] w

@[expose] def ruWN (w : List ℤ) : Array ℕ :=
  wordA 4060 #[ruNs0A, ruNs1A] #[ruInv ruNs0A, ruInv ruNs1A] w

@[expose] def ruBCA : Array ℕ := powA 4060 (ruWC [1, 1, 2]) 2

@[expose] def ruCCA : Array ℕ := powA 4060 ruC0A 4

@[expose] def ruXCA : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 ruJGensA[0]! ruBCA) (ruInv ruJGensA[0]!)) (ruInv ruBCA)

@[expose] def ruCNA : Array ℕ := powA 4060 (ruWN [1, 2]) 2

@[expose] def ruXNA : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 ruKGensA[0]! ruNs1A) (ruInv ruKGensA[0]!)) (ruInv ruNs1A)

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
