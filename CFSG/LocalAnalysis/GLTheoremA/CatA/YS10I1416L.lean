module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def chev2L34 : TauCeti.CFSGIndex → Prop
  | .lie i =>
    match i.1 with
    | .A 2 q => q.card = 4
    | _ => False
  | _ => False

@[expose] def chev2Spor (i : TauCeti.CFSGIndex) : Prop :=
  chev2Small i ∨ chev2L34 i

@[expose] def Chev2SporRank : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J → Odd (Nat.card (Subgroup.center J)) →
    catalogIs (J ⧸ Subgroup.center J) chev2Spor → twoRank J < 6

theorem chev2Spor_of_small {i : TauCeti.CFSGIndex} (h : chev2Small i) : chev2Spor i :=
  Or.inl h

theorem catalogIs_chev2Spor_of_small {S : Type} [Group S] (h : catalogIs S chev2Small) :
    catalogIs S chev2Spor :=
  let ⟨i, hi, e⟩ := h
  ⟨i, chev2Spor_of_small hi, e⟩

end CFSG.LocalAnalysis.GLTheoremA

end
