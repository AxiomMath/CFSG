module

public import CFSG.Foundations.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

abbrev A4 : Type := ↥(alternatingGroup (Fin 4))

@[expose] def IsCommProd (Q : Type) [Group Q] {G : Type} [Group G] (N : Subgroup G) : Prop :=
  ∃ S : Finset (Subgroup G), (∀ F ∈ S, Nonempty (↥F ≃* Q)) ∧
    (S : Set (Subgroup G)).Pairwise (fun F F' => ⁅F, F'⁆ = ⊥) ∧ S.sup id = N

@[expose] def NOne (G : Type) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ IsCommProd SL23 N}

@[expose] def NTwo (G : Type) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ IsCommProd A4 N}

@[expose] def EPlus (G : Type) [Group G] : Subgroup G := layer G ⊔ NOne G ⊔ NTwo G

@[expose] def LPlus (X : Type) [Group X] : Subgroup X :=
  (EPlus (X ⧸ pPrimeCore 2 X)).comap (QuotientGroup.mk' (pPrimeCore 2 X))

@[expose] def oTwoPrimeOf {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

section Basic

variable {G G' : Type} [Group G] [Group G']

theorem isCommProd_bot (Q : Type) [Group Q] : IsCommProd Q (⊥ : Subgroup G) :=
  ⟨∅, by simp, by simp, by simp⟩

theorem NOne_normal : (NOne G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem NTwo_normal : (NTwo G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem le_NOne {N : Subgroup G} (hN : N.Normal) (h : IsCommProd SL23 N) : N ≤ NOne G :=
  le_sSup ⟨hN, h⟩

theorem le_NTwo {N : Subgroup G} (hN : N.Normal) (h : IsCommProd A4 N) : N ≤ NTwo G :=
  le_sSup ⟨hN, h⟩

theorem oTwoPrimeOf_le (H : Subgroup G) : oTwoPrimeOf H ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => hx.1

theorem oTwoPrimeOf_mono {H K : Subgroup G} (h : H ≤ K) : oTwoPrimeOf H ≤ oTwoPrimeOf K :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem mem_oTwoPrimeOf {H : Subgroup G} {x : G} (hx : x ∈ H) (k : ℕ) (hk : x ^ (2 ^ k) = 1) :
    x ∈ oTwoPrimeOf H :=
  Subgroup.subset_closure ⟨hx, k, hk⟩

end Basic

end CFSG.OddStandard.Solomon75
