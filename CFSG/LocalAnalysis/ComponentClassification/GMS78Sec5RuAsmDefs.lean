module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPi7
public import Certificates.Data.GMS78RuAsmData

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7

@[expose] noncomputable def pi7Word (w : List (Fin 7 × Bool)) : Pi7 :=
  PresentedGroup.mk _ (FreeGroup.mk w)

@[expose] noncomputable def letterSub (l : List (Fin 7)) : Subgroup Pi7 :=
  closure ((fun i => (PresentedGroup.of i : Pi7)) '' {i | i ∈ l})

@[expose] noncomputable def ruM1 : Subgroup Pi7 := letterSub [0, 1, 2, 3, 4, 5]

@[expose] noncomputable def ruM2 : Subgroup Pi7 := letterSub [0, 1, 2, 3, 4, 6]

@[expose] noncomputable def ruM12 : Subgroup Pi7 := letterSub [0, 1, 2, 3, 4]

@[expose] noncomputable def ruM13 : Subgroup Pi7 := letterSub [0, 1, 2, 3, 5]

@[expose] noncomputable def ruB0 : Subgroup Pi7 := letterSub [0, 1, 2, 3]

@[expose] noncomputable def ruZ0 : Pi7 := pi7Word ruZ0Word

@[expose] noncomputable def ruA0 : Subgroup Pi7 := closure (pi7Word '' {w | w ∈ ruA0Words})

@[expose] noncomputable def ruE0 : Subgroup Pi7 := closure (pi7Word '' {w | w ∈ ruE0Words})

variable {G : Type} [Group G]

@[expose] def IsNormCz {z : G} (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G)))
    (A : Subgroup G) : Prop :=
  (∀ m : ↥ruM1, (m : Pi7) = ruZ0 → ((f₁ m : ↥(centralizer ({z} : Set G))) : G) = z) ∧
    ∀ m : ↥ruM1, (m : Pi7) ∈ ruA0 ↔ ((f₁ m : ↥(centralizer ({z} : Set G))) : G) ∈ A

@[expose] def RuNAIso (A : Subgroup G) : Prop :=
  ∃ f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)),
    ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A

theorem mem_letterSub {l : List (Fin 7)} {i : Fin 7} (hi : i ∈ l) :
    (PresentedGroup.of i : Pi7) ∈ letterSub l :=
  subset_closure ⟨i, hi, rfl⟩

theorem letterSub_mono {l l' : List (Fin 7)} (h : ∀ i ∈ l, i ∈ l') :
    letterSub l ≤ letterSub l' :=
  closure_mono (Set.image_mono fun i hi => h i hi)

end CFSG.ComponentClassification.GMS78.RuAsm
