module

public import CFSG.Certificates.Kernel.LocalQTRankFProved

public section

namespace CFSG.KC.LQT.RF

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem rankF_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (d k fuel dd zi K L : Nat)
    (h : rankFH n w W ta tb prog qp k fuel dd zi K L = true)
    (hp : ∀ j < K, rankFP n w W ta tb prog qp d dd zi (j * L) L = true) :
    RankCert.RankCertS n (List.range n) (slpTabsA ta.toArray tb.toArray prog) qp (d + 1)
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k := by
  apply rankF_sound_proved <;> assumption

end CFSG.KC.LQT.RF

end
