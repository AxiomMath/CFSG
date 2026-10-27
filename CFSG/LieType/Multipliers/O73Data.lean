module

public import CFSG.YGroups.Exact.Y322
public import CFSG.YGroups.Y322Central
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import CFSG.LieType.Multipliers.O73DataInputs
public import Certificates.Certificate10006
public meta import CFSG.YGroups.Defs
public meta import CFSG.YGroups.Exact.Y322
public meta import CFSG.YGroups.Y322Central
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData

public section

namespace CFSG.LieType.Multipliers.O73

open CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native Matrix

theorem code_dec_check : ∀ x : Fin 2187, code (dec x) = x :=
  Certificates.certificate10006.1

theorem vecs_check :
    (∀ i : Fin 8, q3 (vecs i) = 2) ∧ tTabs.size = 8 ∧ rTabs.size = 8 ∧
      (∀ i : Fin 8, tMat (vecs i) * tMat (vecs i) = 1 ∧ rMat (vecs i) * rMat (vecs i) = 1) ∧
      permsOK 2187 tTabs = true ∧ permsOK 2187 rTabs = true ∧
      (∀ i : Fin 8, ∀ x : Fin 2187, q3 (tMat (vecs i) *ᵥ dec x) = q3 (dec x)) :=
  Certificates.certificate10006.2.1

theorem relators_check :
    relatorsOK 2187 tTabs (yRels 3 2 2 ++ eWords) = true ∧
      relatorsOK 2187 rTabs (yRels 3 2 2) = true ∧
      liftArrs.size = 8 ∧ permsOK 1134 liftArrs = true ∧
      relatorsOK 1134 liftArrs eWords = true ∧
      eqA 1134 (evalW 1134 liftArrs spW) (idA 1134) = false :=
  Certificates.certificate10006.2.2.1

theorem beta_check :
    betaArr.size = 728 ∧ (∀ x : Fin 728, betaArr[x.val]! < 2187) ∧
      (∀ x y : Fin 728, betaArr[x.val]! = betaArr[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
        (rTabs[i.val]!)[betaArr[x.val]!]! = betaArr[(y322Arrays[i.val]!)[x.val]!]! :=
  Certificates.certificate10006.2.2.2

end CFSG.LieType.Multipliers.O73
