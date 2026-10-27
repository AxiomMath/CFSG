module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

namespace L246C127

structure CTCert (G : Type) where
  depth : ℕ
  hGens : List G
  nGens : List G
  expo : ℕ

section Check

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R] (enc : G → R)

@[expose] def CTCert.check (c : CTCert G) : Bool :=
  closedH (c.hGens.map enc) (elts enc c.depth c.hGens) &&
  closedH (c.nGens.map enc) (elts enc c.depth c.nGens) &&
  c.nGens.all (fun n => (elts enc c.depth c.hGens).contains (enc n)) &&
  (elts enc c.depth c.hGens).toList.all (fun r => c.nGens.all fun n =>
    (elts enc c.depth c.nGens).toList.any fun n' => r * enc n == n' * r) &&
  (elts enc c.depth c.hGens).toList.all (fun r =>
    !(c.nGens.all fun n => r * enc n == enc n * r) || (elts enc c.depth c.nGens).contains r) &&
  (elts enc c.depth c.nGens).size == 2 ^ c.expo

end Check

open Equiv

@[expose] def memberOK {n : ℕ} (c : LatCert (Perm (Fin n))) (cts : List (CTCert (Perm (Fin n)))) :
    Bool :=
  (c.tGens :: c.lat).all fun L =>
    (elts (RN.enc : Perm (Fin n) → RN n) c.depth L).size == c.msize ||
      cts.any fun ct => ct.hGens == L && ct.check RN.enc

end L246C127

end CFSG.QuasithinUnique
