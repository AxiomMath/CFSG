module

public import CFSG.Certificates.Kernel.LocalQTRankBProved

public section

namespace CFSG.KC.LQT.RB

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem rankB_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (d k fuel dd zi K L PK CK RP RC : Nat) (PT CT : Nat → Nat)
    (h : rankBH n w W B ta tb prog qp k fuel dd zi K L PK CK RP RC PT CT = true)
    (hp : ∀ j < K, rankBP W qp.length (2 ^ k) PT CT d zi (j * L) L = true) :
    RankCert.RankCertS n B (slpTabsA ta.toArray tb.toArray prog) qp (d + 1)
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  apply rankB_sound_proved <;> assumption

end CFSG.KC.LQT.RB

end
