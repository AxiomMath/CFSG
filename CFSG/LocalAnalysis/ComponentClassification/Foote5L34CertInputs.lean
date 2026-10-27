module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.Foote5.L34Unitary

open CFSG.PSL3Four.Native

@[expose] def tpow (t : Tab) : Nat → Tab
  | 0 => idTab 42
  | n + 1 => comp 42 (tpow t n) t

@[expose] def tTab (x s : Tab) : Tab :=
  comp 42 (comp 42 (comp 42 (tpow s 7) x) s) (tpow x 944)

@[expose] def tInvTab (x s : Tab) : Tab :=
  comp 42 (comp 42 (comp 42 x (tpow s 7)) (tpow x 944)) s

@[expose] def wTab (x s : Tab) : Tab :=
  comp 42 (comp 42 (comp 42 (tpow x 944) (tTab x s)) x) (tInvTab x s)

@[expose] def c₄Tabs : Array Tab := centTabs 42 (enumBFS 42 gensS 20160).tabs r₄T

@[expose] def d₁Tabs : Array Tab := (derivedData 42 c₄Tabs (c₄Tabs.map (invTab 42))).1

@[expose] def d₂Tabs : Array Tab := (derivedData 42 d₁Tabs (d₁Tabs.map (invTab 42))).1

@[expose] def unitaryAt (x : Tab) : Bool :=
  !(comp 42 x r₄T == comp 42 r₄T x) || c₄Tabs.contains x || !(tpow x 945 == idTab 42) ||
    c₄Tabs.any fun s => tpow s 8 == idTab 42 && !(d₂Tabs.contains (wTab x s))

@[expose] def unitaryCheck : Bool := (enumBFS 42 gTabs 241920).tabs.all unitaryAt

end CFSG.ComponentClassification.Foote5.L34Unitary
