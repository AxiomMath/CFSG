module

public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Fi22Snd.Graph
import CFSG.Certificates.Kernel.Fi22Snd.Colour

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum CFSG.KS.Raw CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore.Native

theorem graph_sound {n d ng : Nat} {gens : Array (Array Nat)} {R M S G T : Nat → Nat}
    {root : List Nat} (hn0 : 0 < n) (hn : n < 4096) (hd : 0 < d) (hd' : d < 65536)
    (hgs : gens.size = ng) (hG : ∀ k < ng, gens[k]! = unpack n 12 (G k))
    (hrow : ∀ x < n, rowOK n d R M S x = true)
    (himg : ∀ k < ng, ∀ x < n, imgOK n d (G k) R M x = true)
    (htree : ∀ x < n, treeOK n ng G T x = true) (hsym : ∀ i < d, sym0OK R M i = true)
    (hroot : root = decodeRow d (R 0)) :
    adjSearch n gens root = rowsArr n d R ∧ adjOK n gens (rowsArr n d R) root = true := by
  exact CFSG.KC.Fi22Snd.graph_sound' hn0 hgs hG hrow himg htree hsym hroot

theorem img_sound {n d P : Nat} {g : Array Nat} {R M S : Nat → Nat} (hd : 0 < d)
    (hrow : ∀ x < n, rowOK n d R M S x = true) (hg : g = unpack n 12 P)
    (himg : ∀ x < n, imgOK n d P R M x = true) :
    allLt n (fun x => (rowsArr n d R)[g[x]!]! == imgSorted g (rowsArr n d R)[x]!) = true := by
  exact CFSG.KC.Fi22Snd.img_sound' hrow hg himg

theorem root_sound {n d Z : Nat} {R M S : Nat → Nat} (hn : 0 < n) (hd : 0 < d)
    (hrow : rowOK n d R M S 0 = true) (hr : ∀ i < n, rootOK M Z i = true) :
    decodeRow d (R 0) = (List.range n).filter fun i => i != 0 && (unpack n 12 Z)[i]! == i := by
  exact CFSG.KC.Fi22Snd.root_sound' hrow hr

theorem bounds_sound {n d k T P : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {R M S : Nat → Nat} {pts bounds : List Nat} (hn0 : 0 < n) (hn : n < 4096) (hd : 0 < d)
    (hd' : d < 65536) (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hlen : pts.length = bounds.length) (hpts : pts.length < 65536)
    (hcell : ∀ s < pts.length, cellK n S T pts k s (bounds.getD s 0) = true)
    (hinj : injK n S T pts k P = true) :
    boundsOK n nbr t pts bounds k = true := by
  exact CFSG.KC.Fi22Snd.bounds_sound' hn hnbr hrow hsym ht hlen hpts hcell hinj

end CFSG.KC.N3153

end
