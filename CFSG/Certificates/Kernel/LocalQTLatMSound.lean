module

public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.Certificates.Kernel.LocalQTLatSound
import CFSG.Certificates.Kernel.LocalQTLatSixCSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheckDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

theorem allN_intro {m : ℕ} {f : ℕ → Bool} (h : ∀ j < m, f j = true) :
    CFSG.KC.LQT.P.allN m f = true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e : CFSG.KC.LQT.P.allN (m + 1) f = CFSG.KC.Ord.andB (f m) (CFSG.KC.LQT.P.allN m f) := rfl
    rw [e, h m (Nat.lt_succ_self m), ih fun j hj => h j (Nat.lt_succ_of_lt hj)]
    rfl

theorem grpC_intro {n F d : ℕ} {lv : Lvl} {C : List Lvl} {G : List ℕ} {W : List (List (List ℕ))}
    (hg : CFSG.KC.LQT.P.allL G (inC n (lv :: C) F) = true) (hw : wordsC n (lv :: C) G W d = true)
    (hc : ∀ j < n, chainChunk n (lv :: C)
      (fun s => CFSG.KC.LQT.P.allL G fun g => inC n (lv :: C) F (CFSG.KC.LQT.P.mul n s g)) j =
        true) :
    grpC n (lv :: C) F G W d = true := by
  have e : allChain n (lv :: C)
      (fun s => CFSG.KC.LQT.P.allL G fun g => inC n (lv :: C) F (CFSG.KC.LQT.P.mul n s g)) =
      CFSG.KC.LQT.P.allN n (chainChunk n (lv :: C)
        (fun s => CFSG.KC.LQT.P.allL G fun g => inC n (lv :: C) F (CFSG.KC.LQT.P.mul n s g))) :=
    rfl
  rw [grpC, hg, hw, e, allN_intro hc]
  rfl

theorem grpM_of_grpC {n F d : ℕ} {C : List Lvl} {MG : List ℕ} {w : List (List ℕ)}
    {MW : List (List (List ℕ))} (h : grpC n C F MG (w :: MW) d = true) :
    grpM n C F d MG (w :: MW) = true := h

theorem latC_intro {n d msz : ℕ} {C : List Lvl} {MG T sizes : List ℕ} {lat : List (List ℕ)}
    {MW : List (List (List ℕ))} {ms : List Mem} {reps : List (ℕ × ℕ × List (List ℕ))}
    {joins : List (ℕ × ℕ × ℕ × List (List ℕ))}
    (h0 : memsOK T lat ms = true) (h1 : closedOKC n C (chainF C) d MG MW ms = true)
    (h2 : coverC n C (chainF C) (bfsM n C (chainF C) T d) reps = true)
    (h3 : repsC n C (chainF C) T (membersX n C (chainF C) d ms) reps = true)
    (h4 : joinsC n C (chainF C) (membersX n C (chainF C) d ms) joins = true)
    (h5 : sizesC (chainF C) (membersX n C (chainF C) d ms) sizes msz = true)
    (h6 : tleC n C (chainF C) T = true) :
    latC n C d MG MW T lat ms reps joins sizes msz = true := by
  rw [latC, h0, h1, h2, h3, h4, h5, h6]
  rfl

theorem latC_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (MW : List (List (List ℕ)))
    (ms : List Mem) (c : LatCert (Perm (Fin n)))
    (h : latC n C c.depth (c.mGens.map code) MW (c.tGens.map code) (c.lat.map (List.map code)) ms
      (repsCode c) c.joins c.sizes c.msize = true) : c.check RN.enc = true :=
  CFSG.KC.LQT.CM.latC_sound hn C hI MW ms c h

open CFSG.QuasithinUnique.L246C127 in
theorem memberC_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (cts : List (CTCert (Perm (Fin n))))
    (h : memberC n C c.depth (c.tGens.map code) (c.lat.map (List.map code)) ms c.msize
      (cts.map fun ct => (ct.depth, ct.hGens.map code, ct.nGens.map code, ct.expo)) = true) :
    memberOK c cts = true :=
  CFSG.KC.LQT.CM.memberC_sound hn C hI ms c cts h

theorem tleCC_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (MW : List (List (List ℕ)))
    (c : LatCert (Perm (Fin n)))
    (h : tleCC n C c.depth (c.mGens.map code) MW (c.tGens.map code) = true) :
    c.tleOK RN.enc = true :=
  CFSG.KC.LQT.CM.tleCC_sound hn C hI MW c h

open CFSG.QuasithinUnique.A5.G3 in
theorem latSix_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (ds : List (AData n))
    (h : latSixC n C c.depth (c.tGens.map code) (c.lat.map (List.map code)) ms c.sizes
      (ds.map fun A => (A.gens.map code, A.perf)) = true) : latSixCheck c ds = true :=
  CFSG.KC.LQT.CM.latSix_sound hn C hI ms c ds h

theorem containsC_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (A : List (Perm (Fin n))) {d k s : ℕ}
    (h : containsC n C d (c.tGens.map code) (c.lat.map (List.map code)) ms c.sizes (A.map code) k
      s = true) :
    (List.range k).all (fun j => c.sizes.getD j 0 != s ||
      A.all fun g => (elts (RN.enc : Perm (Fin n) → RN n) d ((c.tGens :: c.lat).getD j [])).contains
        (RN.enc g)) = true :=
  CFSG.KC.LQT.CM.containsC_sound hn C hI ms c A h

end CFSG.KC.LQT.L

end
