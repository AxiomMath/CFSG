module

public import Certificates.Data.Kernel.Misc.O73
public import CFSG.Certificates.Kernel.Misc.O73Defs
import CFSG.Certificates.Kernel.Spor.PK.O73

public section

namespace CFSG.KC.Misc.O73

open CFSG.LieType.Multipliers.O73 CFSG.YGroups CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native
  Matrix

theorem vecs_eq : vecs = vecsG vecList := rfl
theorem tTabs_eq : tTabs = tTabsG vecList := rfl
theorem rTabs_eq : rTabs = rTabsG vecList := rfl

theorem o73_sound {VL : List (List ℕ)} {R1 E : List (List ℕ)} {sp : List ℕ}
    {Ts Rs cL cB cY LP YP : List ℕ} {BP nE : ℕ}
    (hm : matK VL Ts Rs = true) (hr : relMK Ts Rs R1 E = true)
    (hl : liftTextK cL LP = true) (hE : ∀ k < nE, relPK LP E k 1 = true)
    (hnE : relPK.lenLLN E ≤ nE) (hs : spK LP sp = true)
    (hb : betaK Rs cB cY BP YP = true) (hcL : cL.length < 2 ^ 16) (hcB : cB.length < 2 ^ 16)
    (hcY : cY.length < 2 ^ 16) (hcB10 : 10 ∉ cB) :
    ((∀ i : Fin 8, q3 (vecsG VL i) = 2) ∧ (tTabsG VL).size = 8 ∧ (rTabsG VL).size = 8 ∧
      (∀ i : Fin 8, tMat (vecsG VL i) * tMat (vecsG VL i) = 1 ∧
        rMat (vecsG VL i) * rMat (vecsG VL i) = 1) ∧
      permsOK 2187 (tTabsG VL) = true ∧ permsOK 2187 (rTabsG VL) = true ∧
      (∀ i : Fin 8, ∀ x : Fin 2187, q3 (tMat (vecsG VL i) *ᵥ dec x) = q3 (dec x)))
    ∧ (relatorsOK 2187 (tTabsG VL) (R1 ++ E) = true ∧ relatorsOK 2187 (rTabsG VL) R1 = true ∧
      (parsePerms (strOf cL)).size = 8 ∧ permsOK 1134 (parsePerms (strOf cL)) = true ∧
      relatorsOK 1134 (parsePerms (strOf cL)) E = true ∧
      eqA 1134 (evalW 1134 (parsePerms (strOf cL)) sp) (idA 1134) = false)
    ∧ ((parseNats (strOf cB)).size = 728 ∧ (∀ x : Fin 728, (parseNats (strOf cB))[x.val]! < 2187) ∧
      (∀ x y : Fin 728, (parseNats (strOf cB))[x.val]! = (parseNats (strOf cB))[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
        ((rTabsG VL)[i.val]!)[(parseNats (strOf cB))[x.val]!]! =
          (parseNats (strOf cB))[((parsePerms (strOf cY))[i.val]!)[x.val]!]!) :=
  CFSG.KS.PK.o73_sound' hm hr hl hE hnE hs hb hcL hcB hcY hcB10

end CFSG.KC.Misc.O73

end
