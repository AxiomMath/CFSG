module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HePairs
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def heSTabsW : List (Array ℕ) := heQp.map fun p => heSLP[p.1]!

@[expose] def heL2 : List (Array ℕ) :=
  heSTabsW ++ (heMwLit[2]!).map (wordTabA #[heTa, heTb] 8330)

@[expose] def heL7 : List (Array ℕ) :=
  heSTabsW ++ (heMwLit[7]!).map (wordTabA #[heTa, heTb] 8330)

@[expose] def r2a : QuotGen := ⟨[4, 2, 1, 2, 2], 1, 3⟩

@[expose] def r2b : QuotGen := ⟨[2, 0, 4, 3], 1, 3⟩

@[expose] def q2s : List QuotGen :=
  [⟨[3, 0, 3, 2, 2, 1, 2, 0, 2], 1, 4⟩, ⟨[1, 2, 1, 3, 3, 2, 2, 2], 1, 2⟩, ⟨[1, 2, 2], 1, 4⟩,
    ⟨[3, 1, 1, 1, 0], 1, 4⟩, ⟨[3, 0, 3, 2, 1, 2, 3, 0, 3], 1, 4⟩]

@[expose] def b7a : QuotGen := ⟨[4, 3, 4], 2, 3⟩

@[expose] def q7a : QuotGen := ⟨[1, 0, 2], 1, 2⟩

@[expose] def q7b : QuotGen := ⟨[3], 1, 2⟩

@[expose] def b7p : QuotGen := ⟨[1, 3, 4], 2, 7⟩

@[expose] def q7p : QuotGen := ⟨[3], 1, 2⟩

end CFSG.QuasithinUnique.Vol2Native.L239.HePairs
