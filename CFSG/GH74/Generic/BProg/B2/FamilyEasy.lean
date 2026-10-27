module

public import CFSG.GH74.Generic.BProg.B2.FamilyL2
public import CFSG.GH74.Generic.BProg.B2.GenLocL5
public import CFSG.GH74.Generic.BProg.B2.ListedG5
public import CFSG.GH74.Generic.BProg.B2.WeakSigJ1

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

namespace FamilyEasy

theorem l5 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : PuL5 J) :
    WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc_l5 h)

section G2


theorem g2 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : PuG2Odd J) :
    WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_g2 h)

end G2

section Ree


theorem s4 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : QShape4 J) :
    WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_ree h)

theorem p4 {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (hq : IsQuasisimple J)
    (h : QShape4 J) : WeakSig2TwoG4 J :=
  FamilyGeneric.weakSig2TwoG4_of_genLoc4_simple hs hq (genLoc4_ree h)

end Ree

section J1


open CFSG.Walter CFSG.Open in
theorem genLoc4_s5 {J : Type} [Group J] (h : QShape5 J) : GenLoc4 J := by
  obtain ⟨e⟩ := h
  exact (genLoc_of_mulEquiv (e.trans walterJ1EquivNative.symm).symm genLoc_walterJ1).genLoc4

theorem s5 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : QShape5 J) :
    WeakSig2NormG4 J :=
  FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (genLoc4_s5 h)

theorem p5 {J : Type} [Group J] [Finite J] (hs : IsSimpleGroup J) (hq : IsQuasisimple J)
    (h : QShape5 J) : WeakSig2TwoG4 J :=
  FamilyGeneric.weakSig2TwoG4_of_genLoc4_simple hs hq (genLoc4_s5 h)

end J1

end FamilyEasy

section Fam


theorem listedWeakSigMinFamG5_of
    (hl4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → TA7.PuL4m J → WeakSig2NormG4 J)
    (hl3sq : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → PuL3sq J → WeakSig2NormG4 J)
    (hs1 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape1 J → WeakSig2NormG4 J)
    (hs3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J → WeakSig2NormG4 J)
    (hp3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape3 J →
      WeakSig2TwoG4 J) :
    ListedWeakSigMinFamG5 where
  l5 _ _ _ hq h := FamilyEasy.l5 hq h
  l4 := hl4
  l3sq := hl3sq
  g2 _ _ _ hq h := FamilyEasy.g2 hq h
  s1 := hs1
  s3 := hs3
  s4 _ _ _ hq h := FamilyEasy.s4 hq h
  s5 _ _ _ hq h := FamilyEasy.s5 hq h
  l2 _ _ _ hq h := weakSig2NormG4_of_listedRankOne hq h
  p3 := hp3
  p4 _ _ _ hq hs h := FamilyEasy.p4 hs hq h
  p5 _ _ _ hq hs h := FamilyEasy.p5 hs hq h

end Fam

end CFSG.GH74.Generic.BProg.B2
