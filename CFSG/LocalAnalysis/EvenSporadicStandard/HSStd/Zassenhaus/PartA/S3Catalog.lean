module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.EvenSporadicStandard.HSStd

@[expose] def HaradaOvergroups : Prop :=
  ∀ (D : Type) [Group D] [Finite D], fusionZStar D = ⊥ → ∀ t : D, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) →
    (LieModel ↥(commutator D) .PSL 2 5 2 ∨ LieModel ↥(commutator D) .PSL 3 5 1 ∨
      LieModel ↥(commutator (commutator D)) .PSU 3 5 1 ∨ Nonempty (D ≃* Equiv.Perm (Fin 7)) ∨
      IsSporadic D .M12) →
    ¬ ∃ A : Subgroup D, IsElemAbelian 2 A ∧ Nat.card A = 16

@[expose] def HaradaL34Data : Prop :=
  ∀ (D : Type) [Group D] [Finite D], fusionZStar D = ⊥ → ∀ (t : D) (K : Subgroup D),
    orderOf t = 2 → centralizer ({t} : Set D) = zpowers t ⊔ K → Disjoint (zpowers t) K →
    ∀ eK : ↥K ≃* Equiv.Perm (Fin 5),
    LieModel ↥(commutator (commutator D)) .PSL 3 2 2 →
    ∀ (u : D) (hu : u ∈ K), (eK ⟨u, hu⟩).IsSwap →
      ∃ o ∈ ({u, t * u} : Set D), 7 ∣ Nat.card ↥(centralizer ({o} : Set D)) ∧
        ¬ ∃ g ∈ centralizer ({o} : Set D), g * t * g⁻¹ = t * o

@[expose] def ThreeCentralizer7 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (N : Subgroup Γ), N.Normal → centralizer (N : Set Γ) = ⊥ →
    (Nonempty (↥N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∨
      IsSporadic ↥N .HS ∨ LieModel ↥N .PSU 4 3 1 ∨ LieModel ↥N .PSL 3 3 2 ∨
      LieModel ↥N .PSL 4 3 1) →
    ∀ y : Γ, orderOf y = 3 → ¬ 7 ∣ Nat.card ↥(centralizer ({y} : Set Γ))

@[expose] def FusionA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G)
    (_ : PAB G L t E W z) (a : PA0 L t E z),
    ∀ g ∈ normalizer ((Vsub t a.u : Subgroup G) : Set G),
      ∃ ab ∈ a.Abar, ∃ g' ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) ⊓
          normalizer ((Vsub t a.u : Subgroup G) : Set G), g = ab * g'

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
