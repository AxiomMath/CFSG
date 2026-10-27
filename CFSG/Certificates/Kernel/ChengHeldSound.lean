module

public import Certificates.Data.Kernel.ChengHeldK
public import Certificates.Data.ChengHeldPres
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.ChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.PSL3Four.Native CFSG.OddStandard.ChengHeldData

variable {n w : Nat}

theorem letter_u {gens ginv : Array Tab} {G GI : Nat → Nat}
    (hg : ∀ j < 7, gens[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true)
    (hi : ∀ j < 7, ginv[j]! = unpack n w (GI j) ∧ canonK n w (mask w) (n * w) (GI j) = true)
    (l : Fin 7 × Bool) :
    (if l.2 then gens[l.1.val]! else ginv[l.1.val]!) =
        unpack n w (Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2) ∧
      canonK n w (mask w) (n * w) (Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2) =
        true := by
  cases l.2
  · exact hi l.1.val l.1.isLt
  · exact hg l.1.val l.1.isLt

theorem fold_u {gens ginv : Array Tab} {G GI : Nat → Nat}
    (hg : ∀ j < 7, gens[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true)
    (hi : ∀ j < 7, ginv[j]! = unpack n w (GI j) ∧ canonK n w (mask w) (n * w) (GI j) = true) :
    ∀ (wd : List (Fin 7 × Bool)) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      wd.foldl (fun t l => comp n t (if l.2 then gens[l.1.val]! else ginv[l.1.val]!))
          (unpack n w acc) = unpack n w (wfK n w G GI acc wd) ∧
        canonK n w (mask w) (n * w) (wfK n w G GI acc wd) = true
  | [], acc, h => ⟨rfl, h⟩
  | l :: wd, acc, h => by
    rw [List.foldl_cons, (letter_u hg hi l).1,
      CFSG.KC.L34KSnd.comp_unpack' h (letter_u hg hi l).2]
    exact fold_u hg hi wd _ (canonK_pcomp h (letter_u hg hi l).2)

theorem wordPermTab_unpack {gens ginv : Array Tab} {G GI : Nat → Nat}
    (hg : ∀ j < 7, gens[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true)
    (hi : ∀ j < 7, ginv[j]! = unpack n w (GI j) ∧ canonK n w (mask w) (n * w) (GI j) = true)
    (hsz : szOK n w = true) (wd : List (Fin 7 × Bool)) :
    wordPermTab n gens ginv wd = unpack n w (wfK n w G GI (pidn n w) wd) ∧
      canonK n w (mask w) (n * w) (wfK n w G GI (pidn n w) wd) = true := by
  unfold wordPermTab
  rw [CFSG.KC.L34KSnd.idTab_unpack' hsz]
  exact fold_u hg hi wd _ (CFSG.KC.L34KSnd.canon_pidn hsz)

theorem invK_spec {G GI : Nat → Nat} {k : Nat} (h : invK n w G GI k = true) {j : Nat}
    (hj : j < k) : canonK n w (mask w) (n * w) (GI j) = true ∧
      pcomp n w (mask w) (G j) (GI j) = pidn n w := by
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  cases hc : canonK n w (mask w) (Nat.mul n w) (GI j)
  · rw [hc] at h'
    exact absurd h' Bool.false_ne_true
  · rw [hc] at h'
    exact ⟨rfl, Nat.eq_of_beq_eq_true h'⟩

theorem regRel_of {α : Nat} {G GI : Nat → Nat} (hn : regN α = n) (hsz : szOK n w = true)
    (hs : (regGens α).size = 7)
    (hg : ∀ j < 7, (regGens α)[j]! = unpack n w (G j) ∧
      canonK n w (mask w) (n * w) (G j) = true)
    (hinv : invK n w G GI 7 = true) (hrel : relK n w G GI (regRelWords α) = true) :
    regRelOK α = true := by
  have hI := CFSG.KC.L34KSnd.invsOK_of_pcomp (n := n) (w := w) (gs := regGens α) (ng := 7)
    (G := G) (GI := GI) hs (fun k hk => (hg k hk).1)
    (fun k hk => ⟨(hg k hk).2, (invK_spec hinv hk).1, (invK_spec hinv hk).2⟩)
  have hi : ∀ j < 7, ((regGens α).map (invTab n))[j]! = unpack n w (GI j) ∧
      canonK n w (mask w) (n * w) (GI j) = true := fun j hj => ⟨hI.1 j hj, (invK_spec hinv hj).1⟩
  unfold regRelOK
  simp only [hn, hs, hI.2, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro wd hwd
  have hr := List.all_eq_true.1 hrel wd hwd
  rw [(wordPermTab_unpack hg hi hsz wd).1, CFSG.KC.L34KSnd.idTab_unpack' hsz,
    CFSG.KC.L34KSnd.beq_unpack (wordPermTab_unpack hg hi hsz wd).2
      (CFSG.KC.L34KSnd.canon_pidn hsz)]
  exact hr

theorem regOrder_of {α k : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hn : regN α = n)
    (hsz : szOK n w = true) (hn0 : 0 < n) (hg : GensOK n w k G (regGens α))
    (hh : penumHdK (pidn n w) n n T PL = true)
    (hp : ∀ i < n, penumPtK n w (mask w) (n * w) false G GI k n T PL POS SRT SRI i = true)
    (hreg : Nat.beq (List.ofFn fun i : Fin n => pg w (mask w) (T i.val) 0).eraseDups.length n =
      true) :
    regOrderOK α = true := by
  have henum := penumK_left_sound (cap := n) hsz hg hh hp
  unfold regOrderOK regEnum
  rw [hn, henum.1, henum.2]
  have hl : ((penumRec n w n T PL).tabs.map fun t => t[0]!).toList =
      List.ofFn fun i : Fin n => pg w (mask w) (T i.val) 0 := by
    rw [penumRec_eq, Array.toList_map, Array.toList_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact unpack_get' hn0
  rw [hl, penumRec_eq, Array.size_ofFn, Nat.eq_of_beq_eq_true hreg]
  simp

end CFSG.KC.ChengHeld

end
