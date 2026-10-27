module

public import Certificates.Data.Kernel.LocalQT.Base
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

import CFSG.Certificates.Kernel.LocalQTBaseProved

public section

namespace CFSG.KC.LQT.BC

open CFSG.QuasithinUnique.K1.SporadicPerm

theorem base_sound {n : Nat} (hn : n ≤ 24) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (zn gn gin hn' hin k fuel d : Nat)
    (h : baseK n ta tb prog qp zn gn gin hn' hin k fuel d = true) :
    BaseCertS n (List.range n) (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn' hin
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k :=
  base_sound_proved hn ta tb prog qp zn gn gin hn' hin k fuel d h

end CFSG.KC.LQT.BC

end
