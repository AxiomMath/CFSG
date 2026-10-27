
module

public import Certificates.Data.Kernel.J2Enum
import CFSG.Certificates.Kernel.J2Enum.Count
import CFSG.Certificates.Kernel.J2Enum.Classes
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.KC.J2Enum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

@[expose] def ChainOK3 (n w kS kO BP NS CH : Nat) (PS PSI LR TR TRI : Nat → Nat) (D : List (List Int))
    (S : Array (Array Nat)) (base : Array Nat) : Prop :=
  Binds n w PS kS 3 BP S base ∧
    headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS 3 BP ∧ n ≤ NS * CH ∧
    (∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) ∧
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true

theorem enumCnt_sound {n w kS kO BP NS CH R₁ R₂ : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h1 : canonK n w (mask w) (n * w) R₁ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₁ = true)
    (h2 : canonK n w (mask w) (n * w) R₂ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₂ = true) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 0 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).length =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 1 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).countP
          (pairTest n 7 12 2 3 (arrTable n (unpack n w R₁))) =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 2 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).countP
          (pairTest n 7 12 2 3 (arrTable n (unpack n w R₂))) =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 3 := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  exact CntPf.enumCnt_sound' hb hh hl hNS hs hp h20 h1 h2

theorem enumCntU_sound {n w kS kO BP NS CH U : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (hU : canonK n w (mask w) (n * w) U = true)
    (hUn : ∀ j < kS, siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0
      (pcomp n w (mask w) U (pcomp n w (mask w) (PS j) (pinvS n w (mask w) U))) = true)
    (hU2 : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (pcomp n w (mask w) U U) = true)
    (hUo : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 U = false) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (arrTable n (unpack n w U)) []).length =
      sumF (rcnt (LR 0)) (blkCntU n w LR TR BP U) := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  exact CntPf.enumCntU_sound' hb hh hl hNS hs hp hU hUn hU2 hUo

theorem classes_sound {n w kS kO BP NS CH g N cap mx r s my : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    {GP GIP CI E P L K Ss SI : Nat → Nat} {CS OFF : List Nat} {gens gensInv : Array Table}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base) (hgk : g ≤ kO)
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgp : ∀ l < g, GP l = PS l ∧ GIP l = PSI l) (hkO : kO ≤ g)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K Ss SI N cap j = true)
    (hrep : ∀ i < CS.length, canonK n w (mask w) (n * w) (E (lget OFF i)) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (E (lget OFF i)) = true ∧
      ordTest n mx (arrTable n (unpack n w (E (lget OFF i)))) = true)
    (hN : (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []).length = N) :
    classOK n gens gensInv (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []) cap =
        true ∧
      classTotal n gens gensInv (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) [])
          (filterProducts n (ordTest n my) (chainTables n S base) (idT n) []) cap r s mx my =
        ((List.range CS.length).map fun i => lget CS i *
          (filterProducts n (ordTest n my) (chainTables n S base) (idT n) []).countP
            (pairTest n r s mx my (arrTable n (unpack n w (E (lget OFF i)))))).sum := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  exact CntPf.classes_sound' hb hh hl hNS hs hp hgk hg hgp hkO hoff h hrep hN

end CFSG.KC.J2Enum

end
