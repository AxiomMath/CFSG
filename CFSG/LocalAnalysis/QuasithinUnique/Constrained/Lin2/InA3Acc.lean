module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hyp

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp

section Acc

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem idxTS : S.relIndex T = 2 :=
  (E.h8 G T M H S L D n hcfg).1.1

theorem TnS : T ≤ Subgroup.normalizer (S : Set G) :=
  (E.h8 G T M H S L D n hcfg).1.2.1

theorem TnR : T ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  (E.h8 G T M H S L D n hcfg).1.2.2

theorem OL : pCoreOf 2 L = blockU L :=
  (E.h8 G T M H S L D n hcfg).2.1.1

theorem UQ : blockU L = pCoreOf 2 H :=
  (E.h8 G T M H S L D n hcfg).2.1.2

theorem Rsyl : IsSylowTwoOf (thompsonJ S) L :=
  (E.h8 G T M H S L D n hcfg).2.2.1.2.1

theorem RUU {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    thompsonJ S = blockU L ⊔ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x = centerOf (thompsonJ S) :=
  ⟨((E.h8 G T M H S L D n hcfg).2.2.1.2.2 x hx hxS).1,
    ((E.h8 G T M H S L D n hcfg).2.2.1.2.2 x hx hxS).2.1⟩

theorem ZLcases :
    ∀ x ∈ T, x ∉ S → conjR D x ≤ Subgroup.normalizer (L : Set G) ∧
      (centerOf L = ⊥ ∨ (IsElemAbelian 2 (centerOf L) ∧ Nat.card (centerOf L) = 2 ^ n ∧
        ActsRegularlyOn (conjR D x) (nonIdentity (centerOf L)))) :=
  (E.h8 G T M H S L D n hcfg).2.2.2.1

theorem exists_B : ∃ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B :=
  (E.h8 G T M H S L D n hcfg).2.2.2.2.1

theorem elemU {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    IsElemAbelian 2 (blockU L) ∧ IsElemAbelian 2 (conjR (blockU L) x) ∧
      ∀ E' : Subgroup G, E' ≤ thompsonJ S → IsElemAbelian 2 E' →
        E' ≤ blockU L ∨ E' ≤ conjR (blockU L) x :=
  (E.h8 G T M H S L D n hcfg).2.2.2.2.2.2.1 x hx hxS

theorem GQ_eq : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G) :=
  (E.h11 G T M H S L D n hcfg).1

theorem Zbasic {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) :
    IsElemAbelian 2 Z ∧ Nat.card Z = 2 ^ n ∧ S ≤ Subgroup.normalizer (Z : Set G) :=
  (E.h16 G T M H S L D n hcfg Z hZ).1

theorem Zcases {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) {x : G} (hx : x ∈ T)
    (hxS : x ∉ S) :
    (centerOf L = ⊥ ∧ conjR Z x = Z ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ centerOf (thompsonJ S) = Z ⊔ conjR Z x ∧ Z ⊓ conjR Z x = ⊥) :=
  (E.h16 G T M H S L D n hcfg Z hZ).2.1 x hx hxS

theorem ZTI {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) : fusionIsTI Z :=
  (E.h18 G T M H S L D n hcfg Z hZ).1

theorem Delta_not_fused {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥)
    {x : G} (hx : x ∈ T) (hxS : x ∉ S) {u : G} (hu : u ∈ lin2Delta (thompsonJ S) Z x) (g : G) :
    g⁻¹ * u * g ∉ Z :=
  (((E.h20 G T M H S L D n hcfg Z hZ hc).2 x hx hxS).1 u hu).2.2 g

theorem Rstrong : thompsonJ S = strongClosure (pCoreOf 2 H) T :=
  (E.h21 G T M H S L D n hcfg).1

theorem R_lt_S : thompsonJ S < S :=
  (E.h22 G T M H S L D n hcfg).2

theorem TR_not_cyclic : ¬ ∃ t ∈ T, T = thompsonJ S ⊔ Subgroup.zpowers t :=
  (E.h22 G T M H S L D n hcfg).1

end Acc

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
