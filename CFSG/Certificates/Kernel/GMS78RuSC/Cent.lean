module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

private theorem range'_split (s : Nat) : List.range' s 1024 = List.range' s 256 ++
    (List.range' (s + 256) 256 ++ (List.range' (s + 512) 256 ++ List.range' (s + 768) 256)) := by
  have h1 : List.range' (s + 512) 256 ++ List.range' (s + 512 + 256) 256 =
      List.range' (s + 512) (256 + 256) := List.range'_append_1
  have h2 : List.range' (s + 256) 256 ++ List.range' (s + 256 + 256) 512 =
      List.range' (s + 256) (256 + 512) := List.range'_append_1
  have h3 : List.range' s 256 ++ List.range' (s + 256) 768 = List.range' s (256 + 768) :=
    List.range'_append_1
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
  rw [h1, h2, h3]

private theorem sCentT_eq (m : Nat → Nat → Nat) (u base : Nat) (acc : List Nat) :
    ∀ L : List Nat, sCentT m u base L acc =
      (L.map (· + base)).filter (fun p => Nat.beq (m p u) (m u p)) ++ acc
  | [] => rfl
  | pc :: L => by
    change (fun p => Bool.rec (motive := fun _ => List Nat) (sCentT m u base L acc)
      (List.cons p (sCentT m u base L acc)) (Nat.beq (m p u) (m u p))) (Nat.add pc base) = _
    rw [sCentT_eq m u base acc L, List.map_cons, List.filter_cons]
    simp only [Nat.add_eq]
    cases h : Nat.beq (m (pc + base) u) (m u (pc + base))
    · simp [h]
    · simp [h]

private theorem land255 (x : Nat) : Nat.land x 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

private theorem land7 (x : Nat) : Nat.land x 7 = x % 8 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 3
  simpa using this

private theorem shr (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

@[expose] def CommTests (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat) : Prop :=
  ∀ p, m p u = m u p →
    cDTest DM (Nat.land (Nat.shiftRight p 10) 7) (Nat.land (Nat.shiftRight u 10) 7) = true ∧
    cCTest (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7))
      (neGet 0 DPR (Nat.land (Nat.shiftRight u 10) 7)) (Nat.land u 255) (Nat.land p 255) = true

private theorem blockT (m : Nat → Nat → Nat) (DPR : List Nat) (DM u pd j base : Nat)
    (hb : base = 1024 * pd + 256 * j) (hpd : pd < 8) (hj : j < 4) (hm : CommTests m DPR DM u) :
    ((sFilter 256 fun pc => cCTest (neGet 0 DPR pd) (neGet 0 DPR (Nat.land (Nat.shiftRight u 10) 7))
      (Nat.land u 255) pc).map (· + base)).filter
        (fun p => Nat.beq (m p u) (m u p)) =
      (List.range' base 256).filter (fun p => Nat.beq (m p u) (m u p)) := by
  subst hb
  rw [P117.sFilter_eq, List.range'_eq_map_range, List.filter_map, List.filter_map,
    List.filter_filter]
  have e : (fun x => 1024 * pd + 256 * j + x) = (fun x => x + (1024 * pd + 256 * j)) := by
    funext x; omega
  rw [e]
  congr 1
  apply List.filter_congr
  intro pc hpc
  rw [List.mem_range] at hpc
  simp only [Function.comp]
  cases hg : Nat.beq (m (pc + (1024 * pd + 256 * j)) u) (m u (pc + (1024 * pd + 256 * j)))
  · simp
  · have h := (hm _ (Nat.eq_of_beq_eq_true hg)).2
    have e1 : Nat.land (Nat.shiftRight (pc + (1024 * pd + 256 * j)) 10) 7 = pd := by
      rw [land7, shr]; omega
    have e2 : Nat.land (pc + (1024 * pd + 256 * j)) 255 = pc := by
      rw [land255]; omega
    rw [e1, e2] at h
    simp only [h, hg, Bool.and_self]

private theorem sCentD_eq (m : Nat → Nat → Nat) (DPR : List Nat) (DM u pd : Nat)
    (acc : List Nat) (hpd : pd < 8) (hm : CommTests m DPR DM u) :
    sCentD m DPR DM u pd acc =
      (List.range' (1024 * pd) 1024).filter (fun p => Nat.beq (m p u) (m u p)) ++ acc := by
  unfold sCentD
  dsimp only
  cases hD : cDTest DM pd (Nat.land (Nat.shiftRight u 10) 7)
  · symm
    rw [List.filter_eq_nil_iff.2, List.nil_append]
    intro p hp
    rw [List.mem_range'_1] at hp
    have e1 : Nat.land (Nat.shiftRight p 10) 7 = pd := by
      rw [land7, shr]; omega
    cases hg : Nat.beq (m p u) (m u p)
    · simp
    · have h := (hm p (Nat.eq_of_beq_eq_true hg)).1
      rw [e1, hD] at h
      exact absurd h (by simp)
  · dsimp only
    simp only [Nat.mul_eq, Nat.add_eq]
    simp only [sCentT_eq]
    rw [blockT m DPR DM u pd 0 (1024 * pd) (by omega) hpd (by omega) hm,
      blockT m DPR DM u pd 1 (1024 * pd + 256) (by omega) hpd (by omega) hm,
      blockT m DPR DM u pd 2 (1024 * pd + 512) (by omega) hpd (by omega) hm,
      blockT m DPR DM u pd 3 (1024 * pd + 768) (by omega) hpd (by omega) hm]
    rw [range'_split]
    simp only [List.filter_append, List.append_assoc]

theorem sCent17_eq (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat)
    (hm : CommTests m DPR DM u) :
    sCent17 m DPR DM u = (List.range 8192).filter (fun p => Nat.beq (m p u) (m u p)) := by
  have e : List.range 8192 = List.range' (1024 * 0) 1024 ++ (List.range' (1024 * 1) 1024 ++
      (List.range' (1024 * 2) 1024 ++ (List.range' (1024 * 3) 1024 ++ (List.range' (1024 * 4) 1024 ++
      (List.range' (1024 * 5) 1024 ++ (List.range' (1024 * 6) 1024 ++ List.range' (1024 * 7) 1024)))))) := by
    have h1 : List.range' 0 1024 ++ List.range' (0 + 1024) 7168 = List.range' 0 (1024 + 7168) :=
      List.range'_append_1
    have h2 : List.range' 1024 1024 ++ List.range' (1024 + 1024) 6144 = List.range' 1024 (1024 + 6144) :=
      List.range'_append_1
    have h3 : List.range' 2048 1024 ++ List.range' (2048 + 1024) 5120 = List.range' 2048 (1024 + 5120) :=
      List.range'_append_1
    have h4 : List.range' 3072 1024 ++ List.range' (3072 + 1024) 4096 = List.range' 3072 (1024 + 4096) :=
      List.range'_append_1
    have h5 : List.range' 4096 1024 ++ List.range' (4096 + 1024) 3072 = List.range' 4096 (1024 + 3072) :=
      List.range'_append_1
    have h6 : List.range' 5120 1024 ++ List.range' (5120 + 1024) 2048 = List.range' 5120 (1024 + 2048) :=
      List.range'_append_1
    have h7 : List.range' 6144 1024 ++ List.range' (6144 + 1024) 1024 = List.range' 6144 (1024 + 1024) :=
      List.range'_append_1
    simp only [Nat.reduceAdd] at h1 h2 h3 h4 h5 h6 h7
    rw [List.range_eq_range']
    simp only [Nat.reduceMul]
    rw [h7, h6, h5, h4, h3, h2, h1]
  rw [e]
  show sCentD m DPR DM u 0 (sCentD m DPR DM u 1 (sCentD m DPR DM u 2 (sCentD m DPR DM u 3
    (sCentD m DPR DM u 4 (sCentD m DPR DM u 5 (sCentD m DPR DM u 6 (sCentD m DPR DM u 7 [])))))))
    = _
  rw [sCentD_eq m DPR DM u 0 _ (by norm_num) hm, sCentD_eq m DPR DM u 1 _ (by norm_num) hm,
    sCentD_eq m DPR DM u 2 _ (by norm_num) hm, sCentD_eq m DPR DM u 3 _ (by norm_num) hm,
    sCentD_eq m DPR DM u 4 _ (by norm_num) hm, sCentD_eq m DPR DM u 5 _ (by norm_num) hm,
    sCentD_eq m DPR DM u 6 _ (by norm_num) hm, sCentD_eq m DPR DM u 7 _ (by norm_num) hm]
  simp only [List.filter_append, List.append_nil]

private def keyV (m : Nat → Nat → Nat) (u p : Nat) : Nat :=
  (fun s => Nat.add 1 (Nat.add
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28))) (m p p)

private theorem sKey_eq (m : Nat → Nat → Nat) (u : Nat) : ∀ n : Nat,
    sKey m n u = (((List.range n).filter (fun p => Nat.beq (m p u) (m u p))).map (keyV m u)).sum
  | 0 => rfl
  | n + 1 => by
    change strictN (sKey m n u) (fun a => Bool.rec (motive := fun _ => Nat) a
      (Nat.add a (keyV m u n)) (Nat.beq (m n u) (m u n))) = _
    rw [P117.strictN_eq, sKey_eq m u n, List.range_succ, List.filter_append]
    cases h : Nat.beq (m n u) (m u n)
    · simp [h]
    · simp [h, Nat.add_comm]

private theorem sKeyL_eq (m : Nat → Nat → Nat) (u : Nat) : ∀ C : List Nat,
    sKeyL m u C = (C.map (keyV m u)).sum
  | [] => rfl
  | p :: C => by
    change strictN (sKeyL m u C) (fun a => Nat.add a (keyV m u p)) = _
    rw [P117.strictN_eq, sKeyL_eq m u C, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

theorem sKeyL_filter (m : Nat → Nat → Nat) (u : Nat) :
    sKeyL m u ((List.range 8192).filter (fun p => Nat.beq (m p u) (m u p))) = sKey m 8192 u := by
  rw [sKeyL_eq, sKey_eq]

end CFSG.KC.GMS.SC

end
