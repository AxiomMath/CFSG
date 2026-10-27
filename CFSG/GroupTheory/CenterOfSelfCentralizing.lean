module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.GroupTheory

theorem inf_centralizer_le_inf_centralizer_of_le {G : Type*} [Group G] {T E Q : Subgroup G}
    (hTE : T ≤ E) (hQT : Q ≤ T) (hC : E ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    T ⊓ Subgroup.centralizer (T : Set G) ≤ Q ⊓ Subgroup.centralizer (Q : Set G) :=
  le_inf ((le_inf (inf_le_left.trans hTE)
      (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hQT hx))).trans hC)
    (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hQT hx))

end CFSG.GroupTheory
