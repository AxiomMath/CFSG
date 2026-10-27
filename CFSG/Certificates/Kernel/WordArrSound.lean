module

public import Certificates.Data.Kernel.WordArrK
public import CFSG.Certificates.Kernel.BfsPinAlg
public import Certificates.Data.GrSLitL34FactsFourCubeWit

public section

namespace CFSG.KC.WordArr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

variable {n w : Nat}

theorem foldl_unpack {k : Nat} (hw : szOK n w = true) {gs : Array (Array Nat)} {G : Nat → Nat}
    (hG : ∀ i < k, gs[i]! = unpack n w (G i) ∧ PP n w (G i)) :
    ∀ (wd : List (Fin k × Bool)) (acc : Array Nat) (A : Nat), PP n w A → acc = unpack n w A →
      wd.foldl (fun acc l => compA n acc (if l.2 then gs[l.1.val]! else invCand n gs[l.1.val]!)) acc =
        unpack n w (wd.foldl (fun A l => pcomp n w (mask w) A
          (if l.2 then G l.1.val else pinvS n w (mask w) (G l.1.val))) A) ∧
      PP n w (wd.foldl (fun A l => pcomp n w (mask w) A
          (if l.2 then G l.1.val else pinvS n w (mask w) (G l.1.val))) A)
  | [], acc, A, hA, he => ⟨he, hA⟩
  | l :: wd, acc, A, hA, he => by
    obtain ⟨hg, hp⟩ := hG l.1.val l.1.isLt
    simp only [List.foldl_cons]
    refine foldl_unpack hw hG wd _ _ ?_ ?_
    · cases l.2
      · exact hA.mul hp.inv
      · exact hA.mul hp
    · rw [he, hg]
      cases l.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [invCand_PP hp, compA_PP hA hp.inv]
      · simp only [↓reduceIte]
        rw [compA_PP hA hp]

theorem wordArr_unpack {k : Nat} (hw : szOK n w = true) {gs : Array (Array Nat)} {G : Nat → Nat}
    (hG : ∀ i < k, gs[i]! = unpack n w (G i) ∧ PP n w (G i)) (wd : List (Fin k × Bool)) :
    wordArr n gs wd = unpack n w (wordFK n w G wd) ∧ PP n w (wordFK n w G wd) :=
  foldl_unpack hw hG wd _ _ (PP.id hw) (idA_eq hw)

end CFSG.KC.WordArr

end
