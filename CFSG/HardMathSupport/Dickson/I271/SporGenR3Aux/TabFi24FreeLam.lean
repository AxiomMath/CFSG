module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24FreeFrame
public import Certificates.Certificate17569

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi24

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.HardMathSupport.Dickson.I271.Fi24Free.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

@[expose] def InLam (a : Fin 306936) : Prop :=
  a = pt0 ∨ a = pt1 ∨ a = third pt0 pt1 ∨ a = cA ∨ a = cB ∨ a = third cA cB

theorem comm_smul_smul {x g : J} (hg : x * g = g * x) (p : Fin 306936) :
    x • g • p = g • x • p := by
  rw [← mul_smul, hg, mul_smul]

theorem mem_frLam {a : Fin 306936} :
    a.val ∈ frLam ctx cA.val cB.val ↔ InLam a := by
  unfold frLam InLam
  rw [clsPt_m1, clsPt_m2]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (Or.inl (congrArg Fin.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Fin.val h)))))

section Parts

theorem scan_parts : FreeLamFacts := Certificates.certificate17569

theorem inLam_smul {g : J} (hg : xJ * g = g * xJ) {a : Fin 306936} (ha : InLam a) :
    InLam (g • a) := by
  have h : jR g * xFr = xFr * jR g := by rw [← jR_xJ, ← map_mul, ← map_mul, hg]
  exact scan_parts g h a ha

end Parts

end CFSG.HardMathSupport.Dickson.I271.TabFi24
