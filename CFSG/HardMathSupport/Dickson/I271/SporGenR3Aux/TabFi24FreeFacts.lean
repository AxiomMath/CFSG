module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Free

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native (frG1 frEps frWc0 frWc1)
open CFSG.Sporadic.Fi24 (R J jR cls root)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


@[expose] def fr0 : Fin 306936 := ⟨0, by norm_num⟩

@[expose] def fr1 : Fin 306936 := ⟨305530, by norm_num⟩

@[expose] noncomputable def frA : Fin 306936 := wordElt frWc0 • root

@[expose] noncomputable def frB : Fin 306936 := wordElt frWc1 • root

@[expose] noncomputable def xFr : R := cls fr0 * cls fr1 * (cls frA * cls frB)

@[expose] noncomputable def frE (i : Fin 6) : J := wordElt frEps[i.val]!

structure FreeFrameFacts : Prop where
  nc_01 : cls fr0 * cls fr1 ≠ cls fr1 * cls fr0
  nc_AB : cls frA * cls frB ≠ cls frB * cls frA
  c_0A : cls fr0 * cls frA = cls frA * cls fr0
  c_0B : cls fr0 * cls frB = cls frB * cls fr0
  c_1A : cls fr1 * cls frA = cls frA * cls fr1
  c_1B : cls fr1 * cls frB = cls frB * cls fr1
  disj_A : frA ≠ fr0 ∧ frA ≠ fr1 ∧ frA ≠ cls fr0 • fr1
  disj_B : frB ≠ fr0 ∧ frB ≠ fr1 ∧ frB ≠ cls fr0 • fr1
  disj_M : cls frA • frB ≠ fr0 ∧ cls frA • frB ≠ fr1 ∧ cls frA • frB ≠ cls fr0 • fr1
  conj : jR (wordElt frG1 * wordElt [2]) = xFr * jR (wordElt frG1)
  eps_fix : ∀ i : Fin 6, frE i • fr0 = fr0 ∧ frE i • fr1 = fr1 ∧ frE i • frA = frA ∧
    frE i • frB = frB
  eps_rel : SatisfiesG23Words frE
  eps_ne : ∃ i, frE i ≠ 1

@[expose] def FrLam (a : Fin 306936) : Prop :=
  a = fr0 ∨ a = fr1 ∨ a = cls fr0 • fr1 ∨ a = frA ∨ a = frB ∨ a = cls frA • frB

@[expose] def FreeLamFacts : Prop :=
  ∀ g : J, jR g * xFr = xFr * jR g → ∀ a, FrLam a → FrLam (g • a)

end CFSG.HardMathSupport.Dickson.I271.TabFi24

end
