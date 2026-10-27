module

public import CFSG.Sporadic.Schreier.LyCheckSylow
public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.SporSch.LySylPMulTab
import CFSG.Certificates.Kernel.SporSch.LySylPNextEA
import CFSG.Certificates.Kernel.SporSch.LySylPBfs
import CFSG.Certificates.Kernel.SporSch.LySylPTable
import CFSG.Certificates.Kernel.SporSch.LySylPConv
import CFSG.Certificates.Kernel.SporSch.LySylPDerived

public section

namespace CFSG.KS.SporSch.LySyl

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native

theorem bfs_sound {w S T L H CM RM ONE LV HV kg c cap nS Hh : Nat} {UG E W PL SO SOI C : Nat → Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hU : ∀ k < kg, validM 5 (111 * S) L H (UG k) = true)
    (hE : ∀ i < c, validM 5 (111 * S) L H (E i) = true) (h0 : E 0 = ONE) (hc512 : c ≤ 512)
    (hsort : ∀ i < c, sortB E SO SOI c i = true)
    (hcap : nS * Hh = cap) (hcc : c = cap) (hkg : kg = 6) (hC0 : C 0 = 1) (hCn : C nS = c)
    (hrun : ∀ q < nS, Nat.beq (runB 5 w S 111 T L H CM RM UG E W kg c Hh (Nat.mul q Hh) (C q))
      (C (Nat.succ q)) = true)
    (hpl : ∀ j < c, plOK W PL c j = true) (hPL0 : PL 0 = 0) {us : Array (Array (Array Nat))}
    (hus : us.size = kg ∧ ∀ k < kg, us[k]! = unpackL 111 w S (UG k)) :
    sylowBFS us cap = recOf w S E PL W c kg ∧ sylowEnumOK us cap (recOf w S E PL W c kg) = true := by
  exact LySylP.Bfs.bfs_sound hc hU hE h0 hc512 hsort hcap hcc hkg hC0 hCn hrun hpl hPL0 hus

theorem mulTab_sound {n : Nat} {MT W PL : Nat → Nat} (hn0 : 0 < n) (hn : n ≤ 256)
    (hpl : ∀ j < n, plOK W PL n j = true) (hrow : ∀ i < n, rowOK MT W PL n i = true) :
    mulTabOf n (Array.ofFn (n := n) fun i => parK PL i.val) (Array.ofFn (n := n) fun i => labK PL i.val)
        (Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val) = TBL MT n ∧
      mulTabOK (TBL MT n) n (Array.ofFn (n := n) fun i => parK PL i.val)
        (Array.ofFn (n := n) fun i => labK PL i.val)
        (Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val) = true := by
  exact LySylP.MulTab.mulTab_sound hn0 hn hpl hrow

theorem derived_sound {n nC nD nS len : Nat} {MT CM DT ST : Nat → Nat} {IV : Nat}
    (hn : n ≤ 256) (hD : nD ≤ n) (hiv : ∀ i < n, ivOK MT IV n i = true)
    (hrows : ∀ i < n, Nat.blt (MT i) (Nat.shiftLeft 1 (Nat.mul 8 n)) = true ∧
      ∀ j < n, tmK MT i j < n)
    (hlen : nS * len = n * n) (hS0 : ST 0 = 0)
    (hslice : ∀ s < nS, commsK MT IV n CM len (Nat.mul s len) (Nat.land (ST s) 65535)
      (Nat.shiftRight (ST s) 16) = ST (Nat.succ s))
    (hnC : Nat.land (ST nS) 65535 = nC) (hnC' : nC < 65535) (hDT0 : DT 0 = 0)
    (hdt : dtRun MT CM DT nC nD = nD) :
    derivedTree (TBL MT n) n = (Array.ofFn (n := nD) fun k => b8 (DT k.val) 0,
      Array.ofFn (n := nD) fun k => b8 (DT k.val) 1, Array.ofFn (n := nD) fun k => b8 (DT k.val) 2,
      Array.ofFn (n := nD) fun k => b8 (DT k.val) 3) := by
  exact LySylP.Derived.derived_sound hn hD hiv hrows hlen hS0 hslice hnC hnC' hDT0 hdt

theorem nextEA_sound {n nN : Nat} {MT NM : Nat → Nat} {L L' : List (List Nat)} {CT : Nat → Nat}
    (hn : n ≤ 256) (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hL : ∀ E ∈ L, incL E = true ∧ CFSG.KS.Mathieu.allLtN n E = true)
    (hrun : ∀ t < L.length, eaOne MT NM n nN (maskL (L.getD t [])) (lenL (L.getD t [])) (CT t) =
      CT (Nat.succ t))
    (hC0 : CT 0 = 0) (hCn : CT L.length = nN) (hnN : nN < 1048576) (hlen : L'.length = nN)
    (hNM : ∀ j < nN, listOfM (NM j) n (L'.getD j []) = true) :
    nextEA (TBL MT n) n L = L' ∧ extOK (TBL MT n) n L L' = true := by
  exact LySylP.NextEA.nextEA_sound hn hrows hL hrun hC0 hCn hnN hlen hNM

theorem table_sound {n nD : Nat} {MT DT : Nat → Nat} {IV : Nat} {L1 L2 L3 L4 : List (List Nat)}
    (hn : n = 256) (hiv : ∀ i < n, rowChk MT IV n (dMask DT nD) i = true)
    (hrows : ∀ i < n, ∀ j < n, tmK MT i j < n)
    (hd : dChk MT IV n DT nD = true) (hL4 : L4 = [(e16 ())[0]!.toList, (e16 ())[1]!.toList])
    (he0 : eChk MT n (L4.getD 0 []) = true) (he1 : eChk MT n (L4.getD 1 []) = true)
    (hq : qChk MT IV n qIndices.toList (L4.getD 0 []) (L4.getD 1 []) (fIndex ()) = true)
    (h1 : extOK (TBL MT n) n [[0]] L1 = true) (h2 : extOK (TBL MT n) n L1 L2 = true)
    (h3 : extOK (TBL MT n) n L2 L3 = true) (h4 : extOK (TBL MT n) n L3 L4 = true) :
    tableOK (TBL MT n) n (Array.ofFn (n := nD) fun k => b8 (DT k.val) 0)
      (Array.ofFn (n := nD) fun k => b8 (DT k.val) 1) (Array.ofFn (n := nD) fun k => b8 (DT k.val) 2)
      (Array.ofFn (n := nD) fun k => b8 (DT k.val) 3) L1 L2 L3 L4 38 = true := by
  exact LySylP.Table.table_sound hn hiv hrows hd hL4 he0 he1 hq h1 h2 h3 h4

theorem conv_sound {cs : List Char} {CL : List (Nat × List Int)} (hend : ∀ c ∈ cs.getLast?, c = '\n')
    (h : convK cs CL = true) :
    (((String.ofList cs).splitOn "\n").filter (· != "")).map (fun line =>
      match line.splitOn " : " with
      | [k, w] => (k.toNat!, parseInts w)
      | _ => (0, [])) = CL := by
  exact LySylP.Conv.conv_sound hend h

end CFSG.KS.SporSch.LySyl

end
