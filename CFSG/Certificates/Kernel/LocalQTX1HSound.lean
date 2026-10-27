module

public import CFSG.Certificates.Kernel.LocalQTX1HProved

public section

namespace CFSG.KC.LQT.XH

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1

theorem x1H_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (ta tb : List Nat)
    (prog qp wprog : List (Nat × Nat)) (gn gin hn hin an bn k fuel N : Nat)
    (Gs Z1L Z2L Z3L QcL : List Nat) (GC GIC HC HIC : Nat) (RC SR IS PT CT : Nat → Nat)
    (KB LB KS LS : Nat)
    (h : x1HH n w ta tb prog qp gn gin hn hin k fuel N Gs Z1L Z2L Z3L QcL GC GIC HC HIC = true)
    (hb : ∀ c < KB, x1HB n w W qp.length N Gs RC SR IS PT CT (c * LB) LB = true)
    (hs : ∀ c < KS, x1HS W qp.length N PT CT Z1L Z2L Z3L QcL (c * LS) LS = true)
    (hcov : N ≤ KB * LB ∧ N ≤ KS * LS)
    (hN : x1HN n w RC Z1L QcL GC GIC HC HIC = true)
    (hW : x1HW n w wprog GC HC an bn ta tb = true) :
    qpOK n (slpTabsA ta.toArray tb.toArray prog) qp ∧
    BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!)
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 ∧
    (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1.size = 2 ^ k ∧
    (gn < (slpTabsA ta.toArray tb.toArray prog).size ∧
      gin < (slpTabsA ta.toArray tb.toArray prog).size ∧
      hn < (slpTabsA ta.toArray tb.toArray prog).size ∧
      hin < (slpTabsA ta.toArray tb.toArray prog).size ∧
      an < (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog).size ∧
      bn < (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog).size) ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog)[gn]!
      (slpTabsA ta.toArray tb.toArray prog)[gin]! = true ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog)[hn]!
      (slpTabsA ta.toArray tb.toArray prog)[hin]! = true ∧
    normOK (zSeries (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 1)
      (slpTabsA ta.toArray tb.toArray prog)[gn]! (slpTabsA ta.toArray tb.toArray prog)[gin]! =
        true ∧
    normOK (cenList (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (zSeries (fullTables n (bfsEnumB n (List.range n)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 3))
      (slpTabsA ta.toArray tb.toArray prog)[hn]! (slpTabsA ta.toArray tb.toArray prog)[hin]! =
        true ∧
    notNormOK (cenList (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (zSeries (fullTables n (bfsEnumB n (List.range n)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 3))
      (slpTabsA ta.toArray tb.toArray prog)[gn]! (slpTabsA ta.toArray tb.toArray prog)[gin]! =
        true ∧
    notNormOK (zSeries (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 1)
      (slpTabsA ta.toArray tb.toArray prog)[hn]! (slpTabsA ta.toArray tb.toArray prog)[hin]! =
        true ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog)[an]! = ta.toArray ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog)[bn]! = tb.toArray := by
  apply x1H_sound_proved <;> assumption

end CFSG.KC.LQT.XH

end
