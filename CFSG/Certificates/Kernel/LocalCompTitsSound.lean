module

public import Certificates.Data.Kernel.LocalComp.Tits
public import Certificates.Data.Kernel.LocalComp.TitsChain
public import Certificates.Data.Kernel.LocalComp.TitsBfs
public import CFSG.Certificates.Kernel.LocalCompTits.Defs
import CFSG.Certificates.Kernel.LocalCompTits.Orbit
import CFSG.Certificates.Kernel.LocalCompTits.Basis
import CFSG.Certificates.Kernel.LocalCompTits.TabP
import CFSG.Certificates.Kernel.LocalCompTits.Words
import CFSG.Certificates.Kernel.LocalCompTits.Chain
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.Certificates.Kernel.Spor.RawSound
import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.LocalComp.Tits

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native

theorem orbit_sound {gs : Array (List Nat)} {root cap N : Nat} {TP TG TR : Nat → Nat}
    (h : orbitK gs root cap N TP TG TR = true) :
    (orbitBFS gs root cap).qsort (· < ·) = Array.ofFn (n := N) (fun i => TP i.val) ∧
      gs.map (tableOf ((orbitBFS gs root cap).qsort (· < ·))) =
        Array.ofFn (n := gs.size) (fun s => tabP N (TG s.val)) ∧
      orbitOK N (Array.ofFn (n := N) fun i => TP i.val) gs
        (Array.ofFn (n := gs.size) fun s => tabP N (TG s.val)) = true :=
  CFSG.KC.LocalComp.TitsSound.orbit_sound h

theorem checkPts_sound {N : Nat} {TP : Nat → Nat} {bv CP : List Nat} {pts : Array Nat}
    (hp : pts = Array.ofFn (n := N) (fun i => TP i.val)) (h : checkK N TP bv CP = true) :
    bv.toArray.map (bsearch pts) = (CP.take bv.length).toArray ∧
      basisIdx pts = (CP.drop bv.length).toArray :=
  CFSG.KC.LocalComp.TitsSound.checkPts_sound hp h

theorem invOK_tabP {N P : Nat} (h : permOK N 11 (mask 11) (N * 11) P (pinvS N 11 (mask 11) P) = true)
    (hN : N < 2048) : invOK N (tabP N P) (invT N (tabP N P)) = true :=
  CFSG.KC.LocalComp.TitsSound.invOK_tabP h hN

theorem cubicOK_of_K {TG : Nat → Nat} {CP : List Nat} {D : TitsWitness}
    (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hc : checkPts = CP.toArray) (h : cubicK 1755 11 TG CP D = true) : cubicOK D = true :=
  CFSG.KC.LocalComp.TitsSound.cubicOK_of_K hg hc h

theorem squareOK_of_K {TG : Nat → Nat} {CP : List Nat} {D : TitsWitness}
    (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hc : checkPts = CP.toArray) (h : squareK 1755 11 TG CP D = true) : squareOK D = true :=
  CFSG.KC.LocalComp.TitsSound.squareOK_of_K hg hc h

open CFSG.KC.LocalComp.TitsChain in
theorem letters_sound {TG TL : Nat → Nat} {words : Array (List Int)} {tbls : Array Table}
    (hg : tbls = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (h : lettersOK TG TL words = true) :
    CFSG.Perm.Native.buildLetters 1755 (letterT 1755 tbls) words =
      Array.ofFn (n := 2 * words.size) fun l => tabP 1755 (TL l.val) :=
  CFSG.KC.LocalComp.TitsSound.letters_sound hg h

open CFSG.KC.LocalComp.TitsChain CFSG.Perm.Native in
theorem chain_sound {TL : Nat → Nat} {TT TS TW : Nat → Nat → Nat} {sz : Nat → Nat}
    {CP : List Nat} {letters : Array Table} {base Q qb : Array Nat}
    (hL : letters = Array.ofFn (n := 28) fun l => tabP 1755 (TL l.val))
    (hp : ∀ j < 14, permOK 1755 11 (mask 11) (1755 * 11) (TL (2 * j)) (TL (2 * j + 1)) = true)
    (hcp : CP.length = 56) (hcpN : ∀ t < 56, CP.getD t 0 < 1755)
    (hbase : base = (CP.take 4).toArray) (hQ : Q = CP.toArray) (hqb : qb = Array.range 4)
    (hv : ∀ i < 4, levelOK 56 TL TT TS TW sz CP i = true)
    (hb : ∀ i < 4, bfsOK TL TT TS sz CP i = true) (hd : ∀ i < 4, depthOK TT sz i = true)
    (hs : ∀ i < 4, ∀ c < 28,
      schRange 56 TL TT TS TW sz (tupOf CP) i (levLetters TL CP i) (64 * c) 64 = true)
    (ht : terminalOK 56 TL CP = true) :
    chainOK 1755 letters base Q qb (chainTrees 1755 letters base) 3 = true ∧
      orbitSizes (chainTrees 1755 letters base) = (List.range 4).map sz :=
  CFSG.KC.LocalComp.TitsSound.chain_sound hL hp hcp hcpN hbase hQ hqb hv hb hd hs ht

open CFSG.KC.LocalComp.TitsChain in
theorem span_sound {N : Nat} {TP M : Nat → Nat} {CP : List Nat}
    (hv : ∀ t < CP.length, CP.getD t 0 < N ∧ TP (CP.getD t 0) < 2 ^ 52)
    (h : spanK TP CP M = true) :
    spanOK (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!)
      (spanMasks (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!)) = true :=
  CFSG.KC.LocalComp.TitsSound.span_sound hv h

end CFSG.KC.LocalComp.Tits

end
