module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakInner
public import CFSG.RankThree.GF2n.Tim78S3Setting

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup)
open CFSG.RankThree.PartTwo (omegaOneSub)

variable {G : Type} [Group G]

abbrev sD1 (B : Subgroup G) (g : G) : Subgroup G := conjSubgroup g (omegaTwoSub B)

abbrev sC1 (B : Subgroup G) (g x : G) : Subgroup G := conjSubgroup x (sD1 B g)

abbrev sC0 (B : Subgroup G) (g x : G) : Subgroup G := omegaOneSub (sC1 B g x)

abbrev sA0 (B : Subgroup G) (m : G) : Subgroup G := conjSubgroup m (omegaOneSub B)

abbrev sX (B : Subgroup G) (g x : G) : Subgroup G := dX (sD1 B g) x

abbrev sN (B : Subgroup G) (g x : G) : Subgroup G := dN (sD1 B g) x

abbrev sS2 (B : Subgroup G) (g x : G) : Subgroup G := dS2 (sD1 B g) x

abbrev sS (B : Subgroup G) (g m x : G) : Subgroup G :=
  sS2 B g x ⊓ Subgroup.centralizer (sA0 B m : Set G)

abbrev sF0 (B : Subgroup G) (g m x : G) : Subgroup G :=
  (sX B g x ⊔ sA0 B m) ⊓ Subgroup.centralizer (sX B g x : Set G)

abbrev sE (B : Subgroup G) (g m x : G) : Subgroup G := sS B g m x ⊔ sF0 B g m x

abbrev sV (B : Subgroup G) (g m x : G) : Subgroup G := sC0 B g x ⊔ sF0 B g m x

end CFSG.CGT.PushingUpLit.SolKR2
