module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] def CzS5Fact {G : Type} [Group G] (t z : G) (R0 : Subgroup G) : Prop :=
  ∃ ψ : ↥(centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) →* Equiv.Perm (Fin 5),
    Function.Surjective ψ ∧
      ψ.ker = R0.subgroupOf (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))

@[expose] def Setting25Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ t : G, orderOf t = 2 →
      ∀ E : Subgroup (centralizer ({t} : Set G)),
        TwoHS.IsF5Centralizer (centralizer ({t} : Set G)) E →
          ∃ (z z₁ : G) (ι : Elem2 6 →* G) (zv : V6) (R0 F : Subgroup G),
            Setting25 G t z z₁ ι zv R0 F ∧ ¬ IsConj t z ∧ IsConj t (t * z) ∧ CzS5Fact t z R0 ∧
              Facts210 G t z

@[expose] def Lemma27Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
      ∀ {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6} {R0 F : Subgroup G}
        (h : Setting25 G t z z₁ ι zv R0 F), ¬ IsConj t z → IsConj t (t * z) →
          CzS5Fact t z R0 → Lemma27Out h

end CFSG.EvenSporadicStandard.HNRecog.Harada
