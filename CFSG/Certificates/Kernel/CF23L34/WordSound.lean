module

public import Certificates.Data.Kernel.CF23L34.Word
public import Certificates.Data.GrSLitL34FactsCF23SuzCheck
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KC.CF23L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.GSThmB.CF23L34

variable {n w : Nat}

theorem evK_cons (G GI : Nat → Nat) (l : Fin 2 × Bool) (x : List (Fin 2 × Bool)) :
    evK n w G GI (l :: x) = pcomp n w (mask w) (ltrK G GI l) (evK n w G GI x) :=
  CFSG.KS.PF.strictN_eqP _ _

theorem evalFW_sound (hw : szOK n w = true) {g gi : Array (Array Nat)} {G GI : Nat → Nat}
    (hg : ∀ i < 2, g[i]! = unpack n w (G i) ∧ PP n w (G i))
    (hgi : ∀ i < 2, gi[i]! = unpack n w (GI i) ∧ PP n w (GI i)) :
    ∀ x : List (Fin 2 × Bool),
      evalFW n g gi x = unpack n w (evK n w G GI x) ∧ PP n w (evK n w G GI x)
  | [] => ⟨idA_eq hw, PP.id hw⟩
  | (i, b) :: x => by
    obtain ⟨ih, hp⟩ := evalFW_sound hw hg hgi x
    have hl : (if b then g[i.val]! else gi[i.val]!) = unpack n w (ltrK G GI (i, b)) ∧
        PP n w (ltrK G GI (i, b)) := by
      cases b
      · exact hgi i.val i.isLt
      · exact hg i.val i.isLt
    have e : evalFW n g gi ((i, b) :: x) =
        compA n (if b then g[i.val]! else gi[i.val]!) (evalFW n g gi x) := rfl
    rw [e, evK_cons, hl.1, ih, compA_PP hl.2 hp]
    exact ⟨rfl, hl.2.mul hp⟩

theorem conj_sound {m t y mi : Nat} (hm : PP n w m) (ht : PP n w t) (hy : PP n w y)
    (hmi : pinvS n w (mask w) m = mi)
    (h : Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) m t) mi) (pcomp n w (mask w) t y) = true) :
    eqA n (compA n (compA n (unpack n w m) (unpack n w t)) (invCand n (unpack n w m)))
      (compA n (unpack n w t) (unpack n w y)) = true := by
  rw [invCand_PP hm, compA_PP hm ht, compA_PP (hm.mul ht) hm.inv, compA_PP ht hy,
    eqA_PP ((hm.mul ht).mul hm.inv) (ht.mul hy), hmi]
  exact h

theorem ne_id_sound (hw : szOK n w = true) {p : Nat} (hp : PP n w p)
    (h : Nat.beq p (pidn n w) = false) : (!eqA n (unpack n w p) (idA n)) = true := by
  rw [idA_eq hw, eqA_PP hp (PP.id hw), h]
  rfl

theorem eq_id_sound (hw : szOK n w = true) {p : Nat} (hp : PP n w p)
    (h : Nat.beq p (pidn n w) = true) : eqA n (unpack n w p) (idA n) = true := by
  rw [idA_eq hw, eqA_PP hp (PP.id hw), h]

end CFSG.KC.CF23L34

end
