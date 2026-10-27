module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPi7Equiv
public import Certificates.Data.GMS78RuAsmCheck

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.ComponentClassification.GMS78.RuPi7 CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj

theorem pi7ToJ_pi7Word (w : List (Fin 7 × Bool)) :
    pi7ToJ (pi7Word w) = wordProd pi7Img (ruAsmNatWord w) := by
  have hext : pi7ToJ.comp (PresentedGroup.mk _) =
      FreeGroup.lift (fun i : Fin 7 => pi7Img i.val) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact pi7ToJ_of i
  have h : pi7ToJ (pi7Word w) =
      FreeGroup.lift (fun i : Fin 7 => pi7Img i.val) (FreeGroup.mk w) :=
    DFunLike.congr_fun hext (FreeGroup.mk w)
  rw [h, lift_mk_eq_wordProd]
  rfl

theorem pi7Word_eq_of_wordProd
    {u v : List (Fin 7 × Bool)}
    (h : wordProd pi7Img (ruAsmNatWord u) = wordProd pi7Img (ruAsmNatWord v)) :
    pi7Word u = pi7Word v :=
  pi7ToJ_bijective.1 (by rw [pi7ToJ_pi7Word, pi7ToJ_pi7Word, h])

theorem pi7Word_ne_of_wordProd {u v : List (Fin 7 × Bool)}
    (h : wordProd pi7Img (ruAsmNatWord u) ≠ wordProd pi7Img (ruAsmNatWord v)) :
    pi7Word u ≠ pi7Word v := fun e => h (by rw [← pi7ToJ_pi7Word, ← pi7ToJ_pi7Word, e])

end CFSG.ComponentClassification.GMS78.RuAsm
