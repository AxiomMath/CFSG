module

public import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.BW

open CFSG.QuasithinUnique.K1.SporadicPerm

theorem baseW_sound {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (zn gn gin hn hin k fuel d : Nat)
    (h : baseWK n w B ta tb prog qp zn gn gin hn hin k fuel d = true) :
    BaseCertS n B (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn hin
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k :=
  baseW_sound_proved hw B ta tb prog qp zn gn gin hn hin k fuel d h

end CFSG.KC.LQT.BW

end
