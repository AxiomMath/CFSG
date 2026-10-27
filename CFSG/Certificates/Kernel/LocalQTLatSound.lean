
module

public import Certificates.Data.Kernel.LocalQT.Lat
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def repsCode {n : ℕ} (c : LatCert (Perm (Fin n))) : List (ℕ × ℕ × List (List ℕ)) :=
  c.reps.map fun r => (code r.1, r.2.1, r.2.2)

theorem latK_intro {n d ms : ℕ} {MG T sizes : List ℕ} {lat : List (List ℕ)}
    {reps : List (ℕ × ℕ × List (List ℕ))} {joins : List (ℕ × ℕ × ℕ × List (List ℕ))}
    (h1 : closedOKK n d MG T lat = true) (h2 : coverK n d MG T reps = true)
    (h3 : repsK n T (membersK n d T lat) reps = true)
    (h4 : joinsK n (membersK n d T lat) joins = true)
    (h5 : sizesK n d MG T lat sizes ms = true) (h6 : tleK n d MG T = true) :
    latK n d MG T lat reps joins sizes ms = true := by
  rw [latK, h1, h2, h3, h4, h5, h6]
  rfl

end CFSG.KC.LQT.L

end
