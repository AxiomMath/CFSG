module

public import CFSG.Certificates.Kernel.LocalQTBaseSProved

public section

namespace CFSG.KC.LQT.BS

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BT

theorem baseS_sound {n w : Nat} (hw : n ≤ 2 ^ w) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) (PG : Nat → Nat)
    (h : baseSK n w B ta tb prog qp TF K m RS RT zn gn gin hn hin k fuel M lg E K2 L2 = true)
    (hnd : ∀ c < K, nodesT n w prog TF (c * m) m = true)
    (hs : ∀ c < K2, setS w B qp TF RS RT zn M lg E PG (c * L2) L2 = true) :
    BaseCertS n B (slpTabsA ta.toArray tb.toArray prog) qp zn gn gin hn hin
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  apply baseS_sound_proved <;> assumption

end CFSG.KC.LQT.BS

end
