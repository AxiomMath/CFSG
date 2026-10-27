module

public import Certificates.Data.Kernel.LocalQT.SylE
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen

import CFSG.Certificates.Kernel.LocalQTSylProved
import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace CFSG.KC.LQT.Syl.PfE

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.Syl.Pf
  CFSG.KC.Ord

variable {n : ℕ} (H : Subgroup (Perm (Fin n)))

private theorem map_codeP (L : List H) :
    L.map (fun x : H => codeP (x : Perm (Fin n))) = L.map (cH H) := rfl

private theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

private theorem sqK_succ (n x a : ℕ) : sqK n x (a + 1) = sqK n (P.mul n x x) a := by
  have : sqK n x (a + 1) = letN (P.mul n x x) (fun y => sqK n y a) := rfl
  rw [this, letN_eq]

private theorem sqK_H {H : Subgroup (Perm (Fin n))} (hn : n ≤ 32) (a : ℕ) :
    ∀ x : H, sqK n (cH H x) a = cH H (x ^ (2 ^ a)) := by
  induction a with
  | zero => intro x; show cH H x = cH H (x ^ 2 ^ 0); rw [pow_zero, pow_one]
  | succ a ih =>
    intro x
    rw [sqK_succ, cH_mul hn, ih, ← pow_two, ← pow_mul, pow_succ, mul_comm]

theorem listSylG_sound' (L G : List H) {LC GC : List ℕ} (a : ℕ)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hG : G.map (fun x : H => codeP (x : Perm (Fin n))) = GC) (h : sylG2K n a LC GC = true) :
    L.length = 2 ^ a ∧ L.Nodup ∧ (1 : H) ∈ L ∧ (∀ x ∈ L, ∀ g ∈ G, x * g ∈ L) ∧
      (∀ x ∈ L, x ^ (2 ^ a) = 1) := by
  rw [map_codeP] at hL hG
  subst hL hG
  unfold sylG2K at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  have hn : n ≤ 32 := Nat.le_of_ble_eq_true h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [P.beq_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at h2
    exact h2
  · exact List.Nodup.of_map _ (CFSG.KC.LQT.T2.nodup_of_distinctS h3)
  · rw [CFSG.KC.LQT.S.memL_iff, cH_one, mem_map_cH hn] at h4
    exact h4
  · intro x hx g hg
    have := (P.allL_iff _ _).1 h6 (cH H g) (List.mem_map_of_mem hg)
    rw [eqL_iff] at this
    have hm : cH H (x * g) ∈ List.map (fun y => P.mul n y (cH H g)) (List.map (cH H) L) := by
      rw [List.mem_map]
      exact ⟨cH H x, List.mem_map_of_mem hx, cH_mul hn x g⟩
    rw [← (CFSG.KC.LQT.T2.sortK_perm _).mem_iff, this, (CFSG.KC.LQT.T2.sortK_perm _).mem_iff,
      mem_map_cH hn] at hm
    exact hm
  · intro x hx
    have := (P.allL_iff _ _).1 h5 (cH H x) (List.mem_map_of_mem hx)
    rw [sqK_H hn, cH_one, beq_cH hn] at this
    exact this

theorem sub_sound' (L E : List H) {LC EC : List ℕ} (a : ℕ)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hE : E.map (fun x : H => codeP (x : Perm (Fin n))) = EC) (h : subOK n a LC EC = true) :
    E.length = 2 ^ a ∧ E.Nodup ∧ (1 : H) ∈ E ∧ (∀ x ∈ E, ∀ y ∈ E, x * y ∈ E) ∧
      (∀ x ∈ E, x ∈ L) := by
  rw [map_codeP] at hL hE
  subst hL hE
  unfold subOK at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  have hn : n ≤ 32 := Nat.le_of_ble_eq_true h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [P.beq_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at h2
    exact h2
  · exact List.Nodup.of_map _ (CFSG.KC.LQT.T2.nodup_of_distinctS h3)
  · rw [CFSG.KC.LQT.S.memL_iff, cH_one, mem_map_cH hn] at h4
    exact h4
  · intro x hx y hy
    have := (P.allL_iff _ _).1 ((P.allL_iff _ _).1 h5 (cH H x) (List.mem_map_of_mem hx)) (cH H y)
      (List.mem_map_of_mem hy)
    rw [CFSG.KC.LQT.S.memL_iff, cH_mul hn, mem_map_cH hn] at this
    exact this
  · intro x hx
    have := (P.allL_iff _ _).1 h6 (cH H x) (List.mem_map_of_mem hx)
    rw [CFSG.KC.LQT.S.memL_iff, mem_map_cH hn] at this
    exact this

theorem heavy_sound' (L E : List H) {LC EC : List ℕ} (m c : ℕ) (hn : n ≤ 32)
    (hL : L.map (fun x : H => codeP (x : Perm (Fin n))) = LC)
    (hE : E.map (fun x : H => codeP (x : Perm (Fin n))) = EC)
    (h : lenIs (heavyK n LC EC m) c = true) : (heavyList L E m).length = c := by
  rw [map_codeP] at hL hE
  subst hL hE
  unfold lenIs heavyK at h
  rw [P.beq_iff, lenK_eq, invK_eq hn, CFSG.KC.LQT.T2.filtL_eqT, List.filter_map,
    List.length_map] at h
  rw [← h, heavyList, List.filter_filter]
  congr 1
  refine List.filter_congr fun x _ => ?_
  rw [Function.comp_apply, CFSG.KC.LQT.T2.filtL_eqT, List.filter_map, CFSG.KC.LQT.S.lenL_eq,
    List.length_map]
  have hf : ((invG L).filter ((fun y => andB (notB (Nat.beq y (cH H x))) (P.comm n (cH H x) y)) ∘
      cH H)) = (invG L).filter fun y => decide (y ≠ x ∧ x * y = y * x) := by
    refine List.filter_congr fun y _ => ?_
    rw [Function.comp_apply, Bool.eq_iff_iff, P.andB_iff, P.notB_iff, beq_cH hn, comm_cH hn,
      decide_eq_true_iff]
  rw [hf, Bool.eq_iff_iff, Bool.and_eq_true, P.andB_iff, P.notB_iff, CFSG.KC.LQT.S.memL_iff,
    mem_map_cH hn, Nat.ble_eq]
  simp only [decide_eq_true_eq]
  exact and_comm

end CFSG.KC.LQT.Syl.PfE

end
