module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts2

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

structure HaradaFacts27 (H : Type) [Group H] (E : Subgroup H) (a z b z₁ : H)
    (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) (zv : V6) (R0 F : Subgroup H) : Prop
    extends HaradaFacts2 H E a z b z₁ S T T' W0 ι zv R0 F where
  C_hom : ∃ ψ : ↥(centralizer ({z} : Set H)) →* Equiv.Perm (Fin 5), Function.Surjective ψ ∧
    ψ.ker = R0.subgroupOf (centralizer ({z} : Set H))

@[expose] def HaradaInterface27 : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∃ (a z b z₁ : H) (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) (zv : V6) (R0 F : Subgroup H),
      HaradaFacts27 H E a z b z₁ S T T' W0 ι zv R0 F

end CFSG.EvenSporadicStandard.HNRecog
