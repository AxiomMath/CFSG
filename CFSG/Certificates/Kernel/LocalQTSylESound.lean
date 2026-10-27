module

public import Certificates.Data.Kernel.LocalQT.SylE
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen
public import CFSG.Certificates.Kernel.LocalQTEvalZKProved
import CFSG.Certificates.Kernel.LocalQTSylEProved

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W

variable {n : ℕ} (H : Subgroup (Perm (Fin n)))

theorem codes_gens (hn : n ≤ 32) (gs : List H) {GC : List ℕ}
    (hG : gs.map (fun x : H => codeP (x : Perm (Fin n))) = GC) (rgw : List (List ℤ)) :
    (rgw.map (evalN H gs)).map (fun x : H => codeP (x : Perm (Fin n))) =
      List.map (evalZK n GC) rgw := by
  subst hG
  have hGC : gs.map (fun x : H => codeP (x : Perm (Fin n))) = (gs.map Subtype.val).map codeP := by
    rw [List.map_map]
    rfl
  rw [List.map_map, hGC]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, evalN, normH_eq, evalZK_codeP hn, coe_evalG]

theorem codes_eval (hn : n ≤ 32) (gs : List H) {GC : List ℕ}
    (hG : gs.map (fun x : H => codeP (x : Perm (Fin n))) = GC) (rgw rwords : List (List ℤ)) :
    (rwords.map (evalN H (rgw.map (evalN H gs)))).map (fun x : H => codeP (x : Perm (Fin n))) =
      rlGK n GC rgw rwords := by
  rw [rlGK, ← codes_gens H hn gs hG rgw]
  exact codes_gens H hn (rgw.map (evalN H gs)) rfl rwords

theorem listSylG_sound (L G : List H) {LC GC : List ℕ} (a : ℕ)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hG : G.map (fun x : H => codeP (x : Perm (Fin n))) = GC) (h : sylG2K n a LC GC = true) :
    L.length = 2 ^ a ∧ L.Nodup ∧ (1 : H) ∈ L ∧ (∀ x ∈ L, ∀ g ∈ G, x * g ∈ L) ∧
      (∀ x ∈ L, x ^ (2 ^ a) = 1) := by
  exact PfE.listSylG_sound' H L G a hL hG h

theorem sub_sound (L E : List H) {LC EC : List ℕ} (a : ℕ)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hE : E.map (fun x : H => codeP (x : Perm (Fin n))) = EC) (h : subOK n a LC EC = true) :
    E.length = 2 ^ a ∧ E.Nodup ∧ (1 : H) ∈ E ∧ (∀ x ∈ E, ∀ y ∈ E, x * y ∈ E) ∧
      (∀ x ∈ E, x ∈ L) := by
  exact PfE.sub_sound' H L E a hL hE h

theorem heavy_sound (L E : List H) {LC EC : List ℕ} (m c : ℕ) (hn : n ≤ 32)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hE : E.map (fun x : H => codeP (x : Perm (Fin n))) = EC)
    (h : lenIs (heavyK n LC EC m) c = true) : (heavyList L E m).length = c := by
  exact PfE.heavy_sound' H L E m c hn hL hE h

end CFSG.KC.LQT.Syl

end
