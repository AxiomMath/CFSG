module

public import Certificates.Data.Kernel.SchreierFam.CqK
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.ClassicalInvolution.SmallCases.NobqArr
import CFSG.Certificates.Kernel.Fi22Rk.Side
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.SchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Nobq

variable {n w : Nat}

theorem closureA_succ (gens : List (Array Nat)) (k : Nat) :
    closureA n gens (k + 1) = (closureA n gens k ++
      (closureA n gens k).flatMap fun x => gens.map fun g => compA n x g).eraseDups := by
  simp only [closureA, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem closureA_mono (gens : List (Array Nat)) {k m : Nat} (h : k ≤ m) {x : Array Nat}
    (hx : x ∈ closureA n gens k) : x ∈ closureA n gens m := by
  induction m, h using Nat.le_induction with
  | base => exact hx
  | succ m _ ih =>
    rw [closureA_succ, List.mem_eraseDups]
    exact List.mem_append_left _ ih

theorem closureA_step {gens : List (Array Nat)} {k : Nat} {x g : Array Nat}
    (hx : x ∈ closureA n gens k) (hg : g ∈ gens) : compA n x g ∈ closureA n gens (k + 1) := by
  rw [closureA_succ, List.mem_eraseDups]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, List.mem_map.2 ⟨g, hg, rfl⟩⟩)

theorem foldl_mem_closureA (gens : List (Array Nat)) :
    ∀ (l : List Nat), (∀ i ∈ l, i < gens.length) → ∀ (x : Array Nat) (k : Nat),
      x ∈ closureA n gens k →
      l.foldl (fun x i => compA n x gens[i]!) x ∈ closureA n gens (k + l.length) := by
  intro l
  induction l with
  | nil => exact fun _ x k hx => hx
  | cons i l ih =>
    intro hl x k hx
    have hi : i < gens.length := hl i List.mem_cons_self
    have hg : gens[i]! ∈ gens := by
      rw [getElem!_pos gens i hi]
      exact List.getElem_mem hi
    have := ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) _ (k + 1) (closureA_step hx hg)
    rw [List.foldl_cons, List.length_cons]
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem foldl_unpack {gs : List (Array Nat)} {G : Nat → Nat}
    (hG : ∀ k < gs.length, gs[k]! = unpack n w (G k) ∧ PP n w (G k)) :
    ∀ (l : List Nat), (∀ i ∈ l, i < gs.length) → ∀ X, PP n w X →
      l.foldl (fun x i => compA n x gs[i]!) (unpack n w X) =
        unpack n w (l.foldl (fun x i => pcomp n w (mask w) x (G i)) X) ∧
      PP n w (l.foldl (fun x i => pcomp n w (mask w) x (G i)) X) := by
  intro l
  induction l with
  | nil => exact fun _ X hX => ⟨rfl, hX⟩
  | cons i l ih =>
    intro hl X hX
    have hi : i < gs.length := hl i List.mem_cons_self
    simp only [List.foldl_cons]
    rw [(hG i hi).1, compA_PP hX (hG i hi).2]
    exact ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) _ (hX.mul (hG i hi).2)

theorem PP_of_permOK' {p q : Nat} (hsz : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hc : canonK n w (mask w) (n * w) p = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem invoNe_eq (R X : Nat) : invoNe n w R X = (Nat.beq (pcomp n w (mask w) X X) (pidn n w) &&
    !Nat.beq X (pidn n w) && !Nat.beq X R) := by
  unfold invoNe
  cases Nat.beq (pcomp n w (mask w) X X) (pidn n w) <;> cases Nat.beq X (pidn n w) <;>
    cases Nat.beq X R <;> rfl

theorem cqK_sound {R : Nat} {gs : List (Array Nat)} {G : Nat → Nat} {L : List (List Nat)}
    {fuel : Nat} (hsz : szOK n w = true) (hR : canonK n w (mask w) (n * w) R = true)
    (hG : ∀ k < gs.length, gs[k]! = unpack n w (G k) ∧ PP n w (G k))
    (hL : ∀ l ∈ L, l.length ≤ fuel ∧ ∀ i ∈ l, i < gs.length) {C : Nat}
    (hC : canonK n w (mask w) (n * w) C = true) (h : cqK n w R G L C = true) :
    cqTestA n (unpack n w R) (closureA n gs fuel) (unpack n w C) = true := by
  have hid := PP.id hsz
  unfold cqTestA
  rw [compA_unpack hC hC, eqA_unpack (canonK_pcomp hC hC) hR]
  unfold cqK at h
  cases hb : Nat.beq (pcomp n w (mask w) C C) R
  · rfl
  · rw [hb] at h
    have h' : L.any (fun l => invoNe n w R
        (pcomp n w (mask w) C (cjK n w (wordK n w G l) C))) = true := h
    obtain ⟨l, hl, hx⟩ := List.any_eq_true.1 h'
    obtain ⟨hl1, hl2⟩ := hL l hl
    obtain ⟨eW, hW⟩ := foldl_unpack hG l hl2 _ hid
    have hmem := closureA_mono gs (by simpa using hl1)
      (foldl_mem_closureA (n := n) gs l hl2 (idA n) 0 (by simp [closureA]))
    rw [idA_eq hsz, eW] at hmem
    rw [Bool.not_true, Bool.false_or, List.any_eq_true]
    refine ⟨_, hmem, ?_⟩
    have hWI := (PP.inv hW).1
    have hX : canonK n w (mask w) (n * w) (pcomp n w (mask w) C (cjK n w (wordK n w G l) C)) =
        true := canonK_pcomp hC (canonK_pcomp hW.1 (canonK_pcomp hC hWI))
    rw [CFSG.KC.Fi22RkS.isInvA_PP hW, conjArr, invCand_PP hW, compA_unpack hC hWI,
      compA_unpack hW.1 (canonK_pcomp hC hWI),
      compA_unpack hC (canonK_pcomp hW.1 (canonK_pcomp hC hWI))]
    have e : pcomp n w (mask w) C (pcomp n w (mask w)
        (List.foldl (fun x i => pcomp n w (mask w) x (G i)) (pidn n w) l)
        (pcomp n w (mask w) C (pinvS n w (mask w)
          (List.foldl (fun x i => pcomp n w (mask w) x (G i)) (pidn n w) l)))) =
        pcomp n w (mask w) C (cjK n w (wordK n w G l) C) := rfl
    rw [e, compA_unpack hX hX, idA_eq hsz, eqA_unpack (canonK_pcomp hX hX) hid.1,
      eqA_unpack hX hid.1, eqA_unpack hX hR, Bool.true_and, ← invoNe_eq]
    exact hx

end CFSG.KS.SchreierFam
