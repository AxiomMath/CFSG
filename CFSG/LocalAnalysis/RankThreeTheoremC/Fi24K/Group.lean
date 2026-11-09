module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Data
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Bridge.TwoGen
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen

@[expose] def WK : Array (List ℤ) := fi24SevenData.words ++ fi24kExtra ()

@[expose] noncomputable def sK (j : ℕ) : CFSG.Sporadic.Fi24.J := CFSG.Sporadic.Fi23.slpG
  CFSG.Sporadic.Fi24.genG WK j

structure Fi24KGroup : Prop where
  size_words : fi24SevenData.words.size = 1087
  size_extra : (fi24kExtra ()).size = 2733
  w0 : fi24SevenData.words[0]! = [1]
  w1 : fi24SevenData.words[1]! = [2]
  header : headerOK (fi24kExtra ()) = true
  mixedSec : ∀ m ∈ mixedSecs, secOK WK m.gs m.lo m.hi = true ∧ m.lo ≤ m.ia ∧ m.ia < m.hi ∧
    m.lo ≤ m.ib ∧ m.ib < m.hi
  pureSec : ∀ q ∈ pureSecs, secOK WK (pureGens q.lam) q.lo q.hi = true ∧
    secOK WK [q.ix, q.iy] q.hi q.hi2 = true ∧ q.lo ≤ q.ix ∧ q.ix < q.hi ∧ q.lo ≤ q.iy ∧
    q.iy < q.hi ∧ q.hi ≤ q.oX ∧ q.oX < q.hi2 ∧ q.hi ≤ q.oY ∧ q.oY < q.hi2 ∧ q.hi ≤ q.oh ∧
    q.oh < q.hi2
  comm85 : sK 1085 * sK 67 = sK 67 * sK 1085
  comm86 : sK 1086 * sK 67 = sK 67 * sK 1086
  comm82 : sK 1082 * sK 66 = sK 66 * sK 1082
  comm83 : sK 1083 * sK 66 = sK 66 * sK 1083
  comm84 : sK 1084 * sK 66 = sK 66 * sK 1084
  mixedEq : ∀ m ∈ mixedSecs, sK m.ia = sK 0 ∧ sK m.ib = sK 1
  pureEq : ∀ q ∈ pureSecs,
    (∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      wordProd (img2 (sK q.ix) (sK q.iy)) v = 1) ∧ sK q.ix ≠ 1 ∧ sK q.oX = sK 64 ∧
    sK q.oY = sK 66 ∧ sK q.oh * (sK 64 * sK 66 ^ q.lam) = sK 67 * sK q.oh

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
