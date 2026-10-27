module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab65ACheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

structure Tab6Facts : Prop where
  stab_le : ∀ i : Fin 8, Nat.card ↥(Gx (wordP wordAZ) ⊓ Gx ((tab6Row i).rowP wordAZ)) ≤
    (![384, 1024, 48, 64, 32, 240, 20, 16] : Fin 8 → ℕ) i
  ne : ∀ i : Fin 8, (tab6Row i).rowP wordAZ ≠ wordP wordAZ
  row0 : IsConj (wordP wordAZ) (wordP wordAZ * (tab6Row 0).rowP wordAZ)
  row1 : IsConj (wordP wordZ) (wordP wordAZ * (tab6Row 1).rowP wordAZ)
  row2 : orderOf (wordP wordAZ * (tab6Row 2).rowP wordAZ) = 3
  row3 : orderOf (wordP wordAZ * (tab6Row 3).rowP wordAZ) = 4 ∧
    IsConj (wordP wordZ) ((wordP wordAZ * (tab6Row 3).rowP wordAZ) ^ 2)
  row4 : orderOf (wordP wordAZ * (tab6Row 4).rowP wordAZ) = 4 ∧
    IsConj (wordP wordAZ) ((wordP wordAZ * (tab6Row 4).rowP wordAZ) ^ 2)
  row5 : orderOf (wordP wordAZ * (tab6Row 5).rowP wordAZ) = 5 ∧
    IsConj (wordP fix5C.rep) (wordP wordAZ * (tab6Row 5).rowP wordAZ)
  row6 : orderOf (wordP wordAZ * (tab6Row 6).rowP wordAZ) = 5 ∧
    IsConj (wordP fix5B.rep) (wordP wordAZ * (tab6Row 6).rowP wordAZ)
  row7 : orderOf (wordP wordAZ * (tab6Row 7).rowP wordAZ) = 6 ∧
    IsConj (wordP wordAZ) ((wordP wordAZ * (tab6Row 7).rowP wordAZ) ^ 3)
  sub2 : closure (elemW '' {w | w ∈ (tab6Row 2).stabWords classaz.centGens}) ≤
    P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({(tab6Row 2).repElem wordAZ} : Set (Equiv.Perm (Fin 1408)))
  sub4 : closure (elemW '' {w | w ∈ (tab6Row 4).stabWords classaz.centGens}) ≤
    P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({(tab6Row 4).repElem wordAZ} : Set (Equiv.Perm (Fin 1408)))
  sub6 : closure (elemW '' {w | w ∈ (tab6Row 6).stabWords classaz.centGens}) ≤
    P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({(tab6Row 6).repElem wordAZ} : Set (Equiv.Perm (Fin 1408)))
  sub7 : closure (elemW '' {w | w ∈ (tab6Row 7).stabWords classaz.centGens}) ≤
    P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({(tab6Row 7).repElem wordAZ} : Set (Equiv.Perm (Fin 1408)))
  shape2 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 2).stabWords classaz.centGens})) ≃*
    (DihedralGroup 4 × Sym 3))
  shape4 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 4).stabWords classaz.centGens})) ≃*
    (Elem2 2 × DihedralGroup 4))
  shape6 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 6).stabWords classaz.centGens})) ≃*
    (Z 2 × DihedralGroup 5))
  shape7 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 7).stabWords classaz.centGens})) ≃*
    (Z 2 × DihedralGroup 4))
  mem5A : wordP tab65AWord ∈ Gx (wordP wordAZ) ⊓ Gx ((tab6Row 5).rowP wordAZ)

end CFSG.EvenSporadicStandard.HNRecog.Section3Model

end
