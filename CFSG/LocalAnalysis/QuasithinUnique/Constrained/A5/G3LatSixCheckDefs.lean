module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck

public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def noSixCheck {n : ℕ} (S : Std.HashSet (RN n)) : Bool :=
  S.toList.all fun x => !(x * x * x * x * x * x == 1 && x * x != 1 && x * x * x != 1)

structure AData (n : ℕ) where
  gens : List (Perm (Fin n))
  perf : List (List CommWord)

@[expose] def AData.check {n : ℕ} (d : AData n) (depth : ℕ) : Bool :=
  closedH (d.gens.map RN.enc) (elts RN.enc depth d.gens) &&
    (elts RN.enc depth d.gens).size == 960 && perfOK RN.enc d.gens d.perf &&
    noSixCheck (elts RN.enc depth d.gens)

@[expose] def latSixCheck {n : ℕ} (c : LatCert (Perm (Fin n))) (ds : List (AData n)) : Bool :=
  ds.all (fun d => d.check c.depth) &&
    (List.range (c.tGens :: c.lat).length).all fun j => c.sizes.getD j 0 != 1920 ||
      ds.any fun d => d.gens.all fun g =>
        (elts (RN.enc : Perm (Fin n) → RN n) c.depth ((c.tGens :: c.lat).getD j [])).contains
          (RN.enc g)

end CFSG.QuasithinUnique.A5.G3
