module

public import Certificates.Data.Kernel.SporSch.RuImg
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Mathlib.Data.List.Perm.Subperm
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native

theorem lenNL_eq : ∀ l : List Nat, lenNL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenNL_eq l)

theorem memNL_iff {x : Nat} : ∀ {l : List Nat}, memNL x l = true ↔ x ∈ l
  | [] => by simp [memNL]
  | y :: l => by
    change Bool.rec (motive := fun _ => Bool) (memNL x l) true (Nat.beq x y) = true ↔ x ∈ y :: l
    cases h : Nat.beq x y
    · have hne : x ≠ y := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
      simp [memNL_iff, hne]
    · simp [Nat.eq_of_beq_eq_true h]

theorem allGtNL_spec {x : Nat} : ∀ {l : List Nat}, allGtNL x l = true → ∀ y ∈ l, x < y
  | [], _ => by simp
  | y :: l, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · simpa [Nat.blt_eq] using h1
    · exact allGtNL_spec h2 z hz

theorem incNL_spec : ∀ {l : List Nat}, incNL l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | x :: l, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    exact List.Pairwise.cons (allGtNL_spec h1) (incNL_spec h2)

theorem distImg_spec {w G : Nat} : ∀ {l S : List Nat}, distImg w G l S = true →
    (l.map (pg w (mask w) G)).Nodup ∧ ∀ x ∈ l.map (pg w (mask w) G), x ∉ S
  | [], _, _ => by simp
  | p :: l, S, h => by
    change strictB (pg w (mask w) G p) (fun x => Bool.rec (motive := fun _ => Bool) false
      (distImg w G l (x :: S)) (Bool.rec (motive := fun _ => Bool) true false (memNL x S))) = true
      at h
    have e : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hns : pg w (mask w) G p ∉ S := by
      intro hm
      rw [(memNL_iff).2 hm] at h1
      exact absurd h1 (by decide)
    obtain ⟨hnd, hS⟩ := distImg_spec h2
    refine ⟨List.nodup_cons.2 ⟨fun hm => hS _ hm (List.mem_cons_self), hnd⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hns
    · exact fun hm => hS x hx (List.mem_cons_of_mem _ hm)

theorem tail_spec {n w G : Nat} {M : List Nat} : ∀ {L : List Nat},
    List.rec (motive := fun _ => Bool) true (fun p _ ih =>
      Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false ih
        (memNL (pg w (mask w) G p) M)) (Nat.blt p n)) L = true →
    ∀ p ∈ L, p < n ∧ pg w (mask w) G p ∈ M
  | [], _ => by simp
  | p :: L, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨by simpa [Nat.blt_eq] using h1, memNL_iff.1 h3⟩
    · exact tail_spec h4 q hq

theorem imgK_lt {n w G : Nat} {L M : List Nat} (h : sortImgK n w G L M = true) : ∀ p ∈ L, p < n := by
  obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨_, h4⟩ := (bAnd_iff _ _).1 h
  exact fun p hp => (tail_spec h4 p hp).1

theorem imgK_inc {n w G : Nat} {L M : List Nat} (h : sortImgK n w G L M = true) :
    M.Pairwise (· < ·) := by
  obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
  exact incNL_spec ((bAnd_iff _ _).1 h).1

theorem imgK_sound {n w G : Nat} {L M : List Nat} (h : sortImgK n w G L M = true) :
    imgSorted (unpack n w G) L = M := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  have ht := tail_spec h4
  have hmap : (L.map fun p => (unpack n w G)[p]!) = L.map (pg w (mask w) G) := by
    apply List.map_congr_left
    intro p hp
    have hpn := (ht p hp).1
    rw [unpack, getElem!_pos _ p (by simpa using hpn), Array.getElem_ofFn]
  have hlen : (L.map (pg w (mask w) G)).length = M.length := by
    rw [List.length_map, ← lenNL_eq, ← lenNL_eq]
    exact Nat.eq_of_beq_eq_true h1
  have hnd := (distImg_spec h3).1
  have hsub : L.map (pg w (mask w) G) ⊆ M := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (ht p hp).2
  have hperm : List.Perm (L.map (pg w (mask w) G)) M :=
    (hnd.subperm hsub).perm_of_length_le (Nat.le_of_eq hlen.symm)
  have hM := incNL_spec h2
  unfold imgSorted
  rw [hmap]
  have hs := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp_all; omega) (fun a b => by simp; omega)
    (L.map (pg w (mask w) G))
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true) ?_ hs
    (hM.imp fun hab => by simp; omega) ((List.mergeSort_perm _ _).trans hperm)
  intro a b _ _ hab hba
  simp at hab hba
  omega

end CFSG.KS.SporSch

end
