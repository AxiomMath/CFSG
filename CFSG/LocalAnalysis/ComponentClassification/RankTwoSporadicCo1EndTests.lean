module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BTests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative

@[expose] def co1EndBase : List Rows := [aR, bR, twoBXYRows.1, twoBXYRows.2]

@[expose] def conjR (g x : Rows) : Rows := mul (mul g x) (inv g)

@[expose] def fourR (a b : Rows) : List Rows := [one, a, b, mul a b]

@[expose] def notInR (x : Rows) (L : List Rows) : Bool :=
  validRows x && L.all fun y => validRows y && y != x

@[expose] def co1EndSwapOK (e₂ c₁ c₂ : Rows) : Bool :=
  e₂ == co1E2R && mul aR aR == one && mul e₂ e₂ == one && commR aR e₂ &&
    notInR aR [one] && notInR e₂ [one, aR] &&
    commR c₁ aR && mul c₁ e₂ == mul (mul aR e₂) c₁ &&
    commR c₂ e₂ && mul c₂ aR == mul (mul aR e₂) c₂

@[expose] def co1EndConjOK (e₂ f₁ f₂ g₁ g₂ : Rows) (db : List Nat) : Bool :=
  commR f₁ aR && commR f₁ e₂ && commR f₂ aR && commR f₂ e₂ && notInR f₁ (fourR aR e₂) &&
    g₁ == mul ((fourR aR e₂).getD (db.getD 0 0) one) ((fourR f₁ f₂).getD (db.getD 1 0) one) &&
    g₂ == mul ((fourR aR e₂).getD (db.getD 2 0) one) ((fourR f₁ f₂).getD (db.getD 3 0) one) &&
    notInR g₁ (fourR aR e₂) && notInR g₁ (fourR f₁ f₂)

@[expose] def co1EndElemOK (e₂ c₁ c₂ a b : Rows) (db : List Nat) : Bool :=
  co1EndSwapOK e₂ c₁ c₂ && mul a (inv a) == one && mul b (inv b) == one &&
    co1EndConjOK e₂ (conjR a aR) (conjR a e₂) (conjR b aR) (conjR b e₂) db

@[expose] def co1EndCoreOK (E : List Rows) (idx : List Nat) (db : List Nat) : Bool :=
  co1EndElemOK (entryR E (idx.getD 0 0)) (entryR E (idx.getD 1 0)) (entryR E (idx.getD 2 0))
    (entryR E (idx.getD 3 0)) (entryR E (idx.getD 4 0)) db

@[expose] def co1EndCheck (d : List (List Nat)) (idx : List Nat) (db : List Nat) : Bool :=
  (dag co1EndBase (d.map decWord)).2.2 && co1EndCoreOK (dag co1EndBase (d.map decWord)).1 idx db

end CFSG.ComponentClassification.RankTwoSporadic.Co1
