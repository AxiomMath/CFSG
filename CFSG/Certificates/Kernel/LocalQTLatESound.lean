module

public import Certificates.Data.Kernel.LocalQT.LatE
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.Certificates.Kernel.LocalQTLatSound
import CFSG.Certificates.Kernel.LocalQTDiagExtSound
import CFSG.Certificates.Kernel.LocalQTLatSixCSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

theorem diagExtC_sound {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) {d N M : ℕ}
    (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂))) (CA : List Lvl)
    (WA : List (List (List ℕ))) (CB : List Lvl) (WB : List (List (List ℕ))) (CD : List Lvl)
    (WD : List (List (List ℕ))) (hIA : chainInj n₁ CA = true) (hIB : chainInj n₂ CB = true)
    (hID : chainInj (n₁ + n₂) CD = true)
    (hc : diagExtC n₁ n₂ d (A.map code) (B.map code) N M CA WA CB WB CD WD = true) :
    diagExtOK (RN.enc : Perm (Fin n₁) → RN n₁)
      (RN.enc : Perm (Fin n₂) → RN n₂) d A B N M = true :=
  CFSG.KC.LQT.CM.diagExtC_sound h A B CA WA CB WB CD WD hIA hIB hID hc

theorem perf_sound {n : ℕ} (hn : n ≤ 32) (G : List (Perm (Fin n))) (P : List (List CommWord))
    (h : perfK n (G.map code) P = true) : perfOK (RN.enc : Perm (Fin n) → RN n) G P = true :=
  CFSG.KC.LQT.CM.perf_sound hn G P h

theorem latG_intro {n d msz k L K : ℕ} {C : List Lvl} {MG TG sizes lab : List ℕ}
    {lat : List (List ℕ)} {MW : List (List (List ℕ))} {T : List (List ℕ)} {ms : List MemG}
    {reps : List (ℕ × ℕ × List (List ℕ))} {joins : List (ℕ × ℕ × ℕ × List (List ℕ))}
    (h0 : memsOKG TG lat ms = true) (h1 : chainOK n C = true)
    (h2 : grpT n C (chainF C) MG MW k T L d = true) (h3 : allA ms (closedMG n d) = true)
    (h4 : Option.rec (motive := fun _ => Bool) false
      (fun Tm => coverG n C (chainF C) Tm K lab reps) (getO ms 0) = true)
    (h5 : repsG n TG ms reps = true) (h6 : joinsG n ms joins = true)
    (h7 : sizesG (chainF C) ms sizes msz = true) (h8 : tleC n C (chainF C) TG = true) :
    latG n C d MG MW k T L TG lat ms K lab reps joins sizes msz = true := by
  rw [latG, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

theorem coverG_intro {n F K : ℕ} {C : List Lvl} {Tm : MemG} {lab : List ℕ}
    {reps : List (ℕ × ℕ × List (List ℕ))} (ha : coverA n C F Tm K lab reps = true)
    (hd : coverD n Tm K lab reps = true) (hc : coverN n F Tm reps = true) :
    coverG n C F Tm K lab reps = true := by
  rw [coverG, ha, hd, hc]
  rfl

theorem latG_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (MW : List (List (List ℕ))) (k : ℕ)
    (T : List (List ℕ)) (L : ℕ) (ms : List MemG) (K : ℕ) (lab : List ℕ)
    (hI : chainInj n C = true) (hIm : allA ms (fun m => chainInj n m.2.1) = true)
    (c : LatCert (Perm (Fin n)))
    (h : latG n C c.depth (c.mGens.map code) MW k T L (c.tGens.map code)
      (c.lat.map (List.map code)) ms K lab (repsCode c) c.joins c.sizes c.msize = true) :
    c.check RN.enc = true :=
  CFSG.KC.LQT.CM.latG_sound hn C MW k T L ms K lab hI hIm c h

theorem containsG_sound {n : ℕ} (hn : n ≤ 32) (ms : List MemG)
    (hIm : allA ms (fun m => chainInj n m.2.1) = true) (c : LatCert (Perm (Fin n)))
    (A : List (Perm (Fin n))) {d k s : ℕ}
    (h : containsG n d (c.tGens.map code) (c.lat.map (List.map code)) ms c.sizes (A.map code) k
      s = true) :
    (List.range k).all (fun j => c.sizes.getD j 0 != s ||
      A.all fun g => (elts (RN.enc : Perm (Fin n) → RN n) d ((c.tGens :: c.lat).getD j [])).contains
        (RN.enc g)) = true :=
  CFSG.KC.LQT.CM.containsG_sound hn ms hIm c A h

end CFSG.KC.LQT.L

end
