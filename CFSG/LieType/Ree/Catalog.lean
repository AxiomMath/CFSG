module

public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Ree.Intertwiner
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Ree.ReeTag

open CFSG.Blueprint

theorem tag_G2 : G2.tag = .G2 :=
  rfl

theorem tag_F4 : F4.tag = .F4 :=
  rfl

theorem perm_G2 : G2.perm = reeG2Perm :=
  rfl

theorem perm_F4 : F4.perm = reeF4Perm :=
  rfl

theorem longSet_G2 : G2.longSet = reeG2Long :=
  rfl

theorem longSet_F4 : F4.longSet = reeF4Long :=
  rfl

theorem relationExponent_eq (t : ReeTag) (a : ℕ) (i : Fin t.tag.rank) :
    (if i ∈ t.longSet then t.prime ^ a else t.prime ^ (a + 1)) = t.prime ^ a * t.exponent i := by
  unfold exponent
  split_ifs <;> ring

end CFSG.LieType.Ree.ReeTag
