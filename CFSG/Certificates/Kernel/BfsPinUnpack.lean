module

public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem eqA_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · refine neK_sound ?_
    unfold neK
    rw [hp, hq, h]
  · exact eqK_sound h

theorem invCand_unpack {n w p : Nat}
    (h : permOK n w (mask w) (n * w) p (pinvS n w (mask w) p) = true) :
    invCand n (unpack n w p) = unpack n w (pinvS n w (mask w) p) :=
  (invEqK_sound h).1

theorem binds_of_check {gs : Array (Array Nat)} {n w ng : Nat} {G : Nat → Nat}
    (h : (Nat.beq gs.size ng && allN ng fun k => bindArrK gs[k]! n w (G k)) = true) :
    gs.size = ng ∧ ∀ k < ng, gs[k]! = unpack n w (G k) := by
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun k hk => unpack_eq_of_bindArrK (allN_spec h.2 k hk)⟩

theorem bfsK_canon {n w ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true) :
    ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  unfold bfsK at hk
  simp only [bAnd_iff] at hk
  exact allN_spec hk.2.2.1

theorem getElem!_map_range {N i : Nat} (f : Nat → Array Nat) (h : i < N) :
    ((List.range N).map f)[i]! = f i := by
  rw [getElem!_pos ((List.range N).map f) i (by simpa using h)]
  simp

theorem pts_toList {N : Nat} (f : Nat → Array Nat) :
    (Array.ofFn (n := N) fun i => f i.val).toList = (List.range N).map f := by
  rw [Array.toList_ofFn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem any_eqA_unpack {n w t : Nat} {L : List Nat} (ht : canonK n w (mask w) (n * w) t = true)
    (hL : ∀ q ∈ L, canonK n w (mask w) (n * w) q = true) :
    (L.map (unpack n w)).any (eqA n (unpack n w t)) = L.any (Nat.beq t) := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    rw [List.map_cons, List.any_cons, List.any_cons, eqA_unpack ht (hL q List.mem_cons_self),
      ih fun q' h' => hL q' (List.mem_cons_of_mem q h')]

end CFSG.KC.BfsPin

end
