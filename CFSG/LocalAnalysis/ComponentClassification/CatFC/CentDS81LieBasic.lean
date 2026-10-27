module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.Sporadic.Co2

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem not_isComponent_of_isCharacteristicP {C : Type*} [Group C] [Finite C]
    (h : IsCharacteristicP 2 C) (K : Subgroup C) : ¬ IsComponent K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact OutcomeLocal.not_isComponent_of_selfCentralizing (p := 2) (pCore_normal (p := 2) (G := C))
    (pCore_isPGroup (p := 2) (G := C)) h K

theorem not_isSolvable_co2 : ¬ Group.IsSolvable (Carrier .Co2) := by
  intro hsolv
  haveI : IsSimpleGroup (Carrier .Co2) := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  have hcomm : ∀ a b : Carrier .Co2, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hsolv
  haveI : IsMulCommutative (Carrier .Co2) := ⟨⟨hcomm⟩⟩
  have hprime := (Group.is_simple_iff_prime_card (α := Carrier .Co2)).1 inferInstance
  have hG : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  rw [hG] at hprime
  exact absurd hprime (by norm_num)

theorem not_isSolvable_of_co2_quotient {C : Type*} [Group C]
    (e : C ⧸ pCore 2 C ≃* Carrier .Co2) : ¬ Group.IsSolvable C := by
  intro hC
  haveI : Group.IsSolvable (C ⧸ pCore 2 C) := inferInstance
  exact not_isSolvable_co2 (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

@[expose] def SolvableOrComponent (X : Type) [Group X] (τ : X) : Prop :=
  Group.IsSolvable ↥(centralizer ({τ} : Set X)) ∨
    ∃ K : Subgroup ↥(centralizer ({τ} : Set X)), IsComponent K

@[expose] def OddDichotomy : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    OddLieType X → ∀ τ : X, orderOf τ = 2 → SolvableOrComponent X τ

theorem not_co2_of_solvableOrComponent {X : Type} [Group X]
    [Finite X] (τ : X) (h : SolvableOrComponent X τ)
    (hchar : IsCharacteristicP 2 ↥(centralizer ({τ} : Set X))) :
    ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
      Carrier .Co2) := by
  rintro ⟨e⟩
  rcases h with hs | ⟨K, hK⟩
  · exact not_isSolvable_of_co2_quotient e hs
  · exact not_isComponent_of_isCharacteristicP hchar K hK

theorem ds81OddLie_of_dichotomy (h : OddDichotomy) : DS81OddLie := by
  intro X _ _ _ hna hodd τ hτ hchar _
  exact not_co2_of_solvableOrComponent τ (h X hna hodd τ hτ) hchar

end CFSG.ComponentClassification.CatFC.DS81
