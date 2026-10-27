module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode

@[expose] public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHeChk
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.A5.Kc3SporPerm

def heBC : List Nat := CFSG.Sporadic.He.Native.chainBase.toList

def heEnumC : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB 8330 heBC (heQpC.map fun p => heSLPC[p.1]!) (heQpC.map fun p => heSLPC[p.2]!) 100000

def hePD : PD where
  n := 8330
  B := heBC
  G := heQpC.map fun p => heSLPC[p.1]!
  Gi := heQpC.map fun p => heSLPC[p.2]!
  Ts := heEnumC.1
  par := heEnumC.2.1
  cl := heEnumC.2.2

end CFSG.QuasithinUnique.A5.Kc3SporHeChk
