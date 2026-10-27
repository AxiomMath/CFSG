module

public import Certificates.Data.Kernel.LocalQT.Syl24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PairCover

import CFSG.Certificates.Kernel.LocalQTSyl24Proved
public import CFSG.Certificates.Kernel.LocalQTWordSound

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W

variable {n : ℕ} (H : Subgroup (Perm (Fin n))) (gA gB : H) {cA cB : ℕ}

theorem sylG2_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ)
    (h : sylG2K n a (rlK n cA cB rgw rwords) (List.map (evalZK n [cA, cB]) rgw) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ g ∈ sylowGens H gA gB rgw,
        x * g ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  exact Pf24.sylG2_sound' gA gB hA hB rgw rwords a h

theorem pairLen_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (c : ℕ) (hn : n ≤ 32)
    (h : lenIs (pairK n (invK n (rlK n cA cB rgw rwords))) c = true) :
    (pairG (invG (sylowList H gA gB rgw rwords))).length = c := by
  exact Pf24.pairLen_sound' gA gB hA hB rgw rwords c hn h

theorem g1okP_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords poolW : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32)
    (h : g1okPK n (List.map (evalZK n [cA, cB]) poolW) (rlK n cA cB rgw rwords) G1 p = true) :
    g1ok (sylowList H gA gB rgw rwords)
      (fun ws => ws.map fun w => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) G1 p =
        true := by
  exact Pf24.g1okP_sound' gA gB hA hB rgw rwords poolW G1 p hn h

theorem g2okP_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords poolW : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32)
    (h : g2okPK n (List.map (evalZK n [cA, cB]) poolW) (rlK n cA cB rgw rwords) G2 p = true) :
    g2ok (sylowList H gA gB rgw rwords)
      (fun ws => ws.map fun w => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) G2 p =
        true := by
  exact Pf24.g2okP_sound' gA gB hA hB rgw rwords poolW G2 p hn h

theorem bad_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (c : ℕ) (hc : c < 2 ^ 40) (hn : n ≤ 32)
    (h : atMost (badK n (rlK n cA cB rgw rwords) G2 hs) c = true) :
    (g2coverBad
      (fun x : H => (List.finRange n).foldl (fun acc i => acc * n + ((x : Perm (Fin n)) i).val) 0)
      (sylowList H gA gB rgw rwords) G2).length ≤ c := by
  exact Pf24.bad_sound' gA gB hA hB rgw rwords G2 hs c hc hn h

end CFSG.KC.LQT.Syl

end
