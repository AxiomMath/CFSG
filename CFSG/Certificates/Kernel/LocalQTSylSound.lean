module

public import Certificates.Data.Kernel.LocalQT.Syl
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen

import CFSG.Certificates.Kernel.LocalQTSylProved

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W

variable {n : ℕ} (H : Subgroup (Perm (Fin n))) (gA gB : H) {cA cB : ℕ}

theorem syl_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ) (h : sylK n a (rlK n cA cB rgw rwords) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ y ∈ sylowList H gA gB rgw rwords,
        x * y ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  exact Pf.syl_sound' gA gB hA hB rgw rwords a h

theorem sylG_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ)
    (h : sylGK n a (rlK n cA cB rgw rwords) (List.map (evalZK n [cA, cB]) rgw) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ g ∈ sylowGens H gA gB rgw,
        x * g ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  exact Pf.sylG_sound' gA gB hA hB rgw rwords a h

theorem rank_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (k : ℕ) (hn : n ≤ 32)
    (h : rankK n (invK n (rlK n cA cB rgw rwords)) k = true) :
    forallIndep (invG (sylowList H gA gB rgw rwords)) (fun _ => false) k [] = true := by
  exact Pf.rank_sound' gA gB hA hB rgw rwords k hn h

theorem g1ok_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (p : ℕ) (hn : n ≤ 32)
    (h : g1okK n cA cB (rlK n cA cB rgw rwords) G1 p = true) :
    g1ok (sylowList H gA gB rgw rwords) (fun ws => ws.map (evalN H [gA, gB])) G1 p = true := by
  exact Pf.g1ok_sound' gA gB hA hB rgw rwords G1 p hn h

theorem g2ok_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32) (h : g2okK n cA cB (rlK n cA cB rgw rwords) G2 p = true) :
    g2ok (sylowList H gA gB rgw rwords) (fun ws => ws.map (evalN H [gA, gB])) G2 p = true := by
  exact Pf.g2ok_sound' gA gB hA hB rgw rwords G2 p hn h

theorem g1cov_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (hs : List (ℕ × ℕ))
    (hn : n ≤ 32) (h : g1covK n (rlK n cA cB rgw rwords) G1 hs = true) :
    g1cover (sylowList H gA gB rgw rwords) G1 = true := by
  exact Pf.g1cov_sound' gA gB hA hB rgw rwords G1 hs hn h

theorem g2cov_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (hn : n ≤ 32) (h : g2covK n (rlK n cA cB rgw rwords) G2 hs = true) :
    g2cover (sylowList H gA gB rgw rwords) G2 = true := by
  exact Pf.g2cov_sound' gA gB hA hB rgw rwords G2 hs hn h

theorem g1covL_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (hs : List (ℕ × ℕ))
    (hn : n ≤ 32) (h : g1covK n (rlK n cA cB rgw rwords) G1 hs = true) :
    ((invList H (sylowList H gA gB rgw rwords)).all fun x => G1.any fun e =>
      (sylowList H gA gB rgw rwords).any fun r =>
        r * x * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.1 1) = true := by
  exact Pf.g1covL_sound' gA gB hA hB rgw rwords G1 hs hn h

theorem g2covL_sound (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (hn : n ≤ 32) (h : g2covK n (rlK n cA cB rgw rwords) G2 hs = true) :
    ((pairList H (invList H (sylowList H gA gB rgw rwords))).all fun p => G2.any fun e =>
      (sylowList H gA gB rgw rwords).any fun r =>
        r * p.1 * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.1 1 &&
          r * p.2 * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.2.1 1) = true := by
  exact Pf.g2covL_sound' gA gB hA hB rgw rwords G2 hs hn h

end CFSG.KC.LQT.Syl

end
