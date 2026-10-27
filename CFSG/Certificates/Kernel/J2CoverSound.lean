
module

public import CFSG.Certificates.Kernel.Child3Sound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.J2CoverSnd.Chain
import CFSG.Certificates.Kernel.J2CoverSnd.Closed
import CFSG.Certificates.Kernel.J2CoverSnd.Packed

public section

namespace CFSG.KC.J2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

theorem prodCnt_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    (filterProducts n f (chainTables n S base) (idT n) []).length = prodCnt n w nb LR TR fk :=
  Snd.prodCnt_sound' hb hp hl hf

theorem prodList_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    filterProducts n f (chainTables n S base) (idT n) [] =
        (prodList n w nb LR TR fk).map (fun X => arrTable n (unpack n w X)) ∧
      ∀ X ∈ prodList n w nb LR TR fk, canonK n w (mask w) (n * w) X = true :=
  Snd.prodList_sound' hb hp hl hf

theorem countProducts_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {f : Table → Bool} {fk : Nat → Bool}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hf : ∀ X, canonK n w (mask w) (n * w) X = true → f (arrTable n (unpack n w X)) = fk X) :
    countProducts n f (chainTables n S base) (idT n) = prodCnt n w nb LR TR fk :=
  Snd.countProducts_sound' hb hp hl hf

theorem ordW_unpack {n w m : Nat} {ws : List Nat} (hm : 0 < m)
    (hc : ∀ X ∈ ws, canonK n w (mask w) (n * w) X = true)
    (hne : ws ≠ [] := by exact List.cons_ne_nil _ _) :
    ordW n (ws.map fun X => arrTable n (unpack n w X)) m = ordPK n w m (prodK n w ws) :=
  Snd.ordW_unpack' hm hne hc

theorem commT_unpack {n w X Y : Nat} (hX : canonK n w (mask w) (n * w) X = true)
    (hY : canonK n w (mask w) (n * w) Y = true) :
    commT n (arrTable n (unpack n w X)) (arrTable n (unpack n w Y)) =
      Nat.beq (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X) :=
  Snd.commT_unpack' hX hY

theorem tblFix_unpack {X : Nat} (hX : canonK 315 9 (mask 9) (315 * 9) X = true) :
    CFSG.ComponentClassification.J2Cover.External.tblFix (arrTable 315 (unpack 315 9 X)) =
      CFSG.KC.Misc.ArrEnum.fixK 315 9 X :=
  Snd.tblFix_unpack' hX

theorem pairCount_map {n w : Nat} {L M : List Nat} {r : Table → Table → Bool}
    {rk : Nat → Nat → Bool}
    (h : ∀ x ∈ L, ∀ y ∈ M, r (arrTable n (unpack n w x)) (arrTable n (unpack n w y)) = rk x y) :
    pairCount (L.map fun X => arrTable n (unpack n w X)) (M.map fun X => arrTable n (unpack n w X))
      r = pairCntK L M rk :=
  Snd.pairCount_map' h

theorem siftK_eq {n w kS nb BP G : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hG : canonK n w (mask w) (n * w) G = true) :
    siftA n (rawLevels n S base) base 0 (unpack n w G) =
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G :=
  Snd.siftK_eq' hb hp hl hG

theorem pcomp_assoc {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r = pcomp n w (mask w) p (pcomp n w (mask w) q r) :=
  Snd.pcomp_assoc' hp hq hr

theorem pcomp_id {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p ∧ pcomp n w (mask w) (pidn n w) p = p :=
  Snd.pcomp_id' hp

theorem ord4_unpack {n w R : Nat} (hR : canonK n w (mask w) (n * w) R = true) :
    ordTest n 4 (arrTable n (unpack n w R)) = ord4K n w R :=
  Snd.ord4_unpack' hR

theorem repSizes_sound {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat}
    {CS OFF : List Nat} {gens gensInv : Array Table} {reps : List Table}
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hreps : reps = (List.range CS.length).map fun i => arrTable n (unpack n w (E (lget OFF i))))
    (hoff : offOK CS OFF N = true) (hpos : allL (fun c => Nat.blt 0 c) CS = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) :
    repSizes n gens gensInv reps cap = CS :=
  repSizes_of_rec hg hgc hoff h (allL_pos hpos) hreps

theorem closedOK_sound {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat}
    {CS OFF : List Nat} {gens gensInv : Array Table}
    (hg : gens.size = g ∧ gensInv.size = g ∧ ∀ l < g, gens[l]! = arrTable n (unpack n w (GP l)) ∧
      gensInv[l]! = arrTable n (unpack n w (GIP l)))
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hinv : ∀ l < g, pcomp n w (mask w) (GP l) (GIP l) = pidn n w)
    (hoff : offOK CS OFF N = true) (hpos : allL (fun c => Nat.blt 0 c) CS = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true) (hn : n = 315) :
    ∀ i < CS.length, CFSG.ComponentClassification.J2Cover.Kernel.closedOK gens gensInv
      (conjClosure n gens gensInv (arrTable n (unpack n w (E (lget OFF i)))) cap).1 = true :=
  Snd.closedOK_of_rec hg hgc hinv hoff h (allL_pos hpos) hn

end CFSG.KC.J2Cover

end
