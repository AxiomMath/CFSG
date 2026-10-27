module

public import Certificates.Data.Kernel.Fi22Search2071
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Fi22Snd.Search

public section

namespace CFSG.KC.S2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.Sporadic.FischerOddCore.Native

theorem search_sound {n d np na k chunks T P : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {base SC : List Nat} {pool acc : Array (Array Nat)} {nodes : Array SNode}
    {R M S PL AC DT : Nat → Nat} (hn0 : 0 < n) (hn : n < 4096) (hd : 0 < d) (hd' : d < 65536)
    (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hbase : base.length < 65536) (hpre : ∀ i < nodes.size, (nodes[i]!).pre.length < 65536)
    (hpreN : ∀ i < nodes.size, ∀ x ∈ (nodes[i]!).pre, x < n)
    (hchunks : 0 < chunks) (hpool : pool.size = np) (hPL : ∀ j < np, pool[j]! = unpack n 12 (PL j))
    (hacc : acc.size = na) (hAC : ∀ i < na, acc[i]! = unpack n 12 (AC i))
    (hinj : injK n S T base k P = true)
    (hsc : ∀ e < base.length, srcColK n S T base k e (SC.getD e 0) = true)
    (h0 : 0 < nodes.size) (hroot : (nodes[0]!).pre = [])
    (hnode : ∀ i < nodes.size, nodeK n S T PL np AC na nodes base SC k DT i = true) :
    searchOK n nbr t base pool nodes acc k chunks = true := by
  exact CFSG.KC.Fi22Snd.search_sound' hn hnbr hrow hsym ht hbase hpre hpreN hpool hPL hacc hAC
    hinj hsc h0 hroot hnode

end CFSG.KC.S2071

end
