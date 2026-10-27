module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open

structure K372Setting (X : Type) [Group X] [Finite X] (p : ℕ) (K E S : Subgroup X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  prime : p.Prime
  five_le : 5 ≤ p
  normal : K.Normal
  quasi : CFSG.IsQuasisimple ↥K
  core : CFSG.pPrimeCore p ↥K = ⊥
  elem : IsElemAbelian p E
  card : Nat.card E = p ^ 2
  rank23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
    pRank p (Subgroup.normalizer (T : Set X)) ≤ 3
  rank_gamma : pRank p (rankThreeGamma 1 p E) ≤ 3
  not_le : ¬ K ≤ rankThreeGamma 1 p E
  two : IsPGroup 2 S
  le_normalizer : rankThreeGamma 1 p E ≤ Subgroup.normalizer (S : Set X)

@[expose] def K372Goal {X : Type} [Group X] (p : ℕ) (K S : Subgroup X) : Prop :=
  ¬ S ≤ Subgroup.centralizer (K : Set X) → p = 5 ∧ CFSG.AGLEmbedding.IsFi22 ↥K

theorem K372Setting.goal_of_catalog {X : Type} [Group X] [Finite X] {p : ℕ} {K E S : Subgroup X}
    (h : K372Setting X p K E S)
    (hLie : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ p →
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → K372Goal p K S)
    (hLiep : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p →
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → K372Goal p K S)
    (hAlt : ∀ n : ℕ, 5 ≤ n → Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) →
      K372Goal p K S)
    (hSpor : ∀ s : TauCeti.SporadicName,
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
        K372Goal p K S) :
    K372Goal p K S := by
  have hcat : IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    h.catalog K (Subgroup.center ↥K) inferInstance h.quasi.2.1 h.quasi.2.2
  obtain ⟨i, ⟨φ⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    obtain ⟨a, b, hab⟩ := h.quasi.2.2
    have hc : ∀ x y : (TauCeti.CFSGIndex.cyclic r hr).Group, x * y = y * x :=
      fun x y => mul_comm x y
    exact absurd (φ.injective (by rw [map_mul, map_mul]; exact hc (φ a) (φ b))) hab
  | alternating n hn => exact hAlt n hn ⟨φ⟩
  | lie d =>
    by_cases hp : d.1.characteristic = p
    · exact hLiep d hp ⟨φ⟩
    · exact hLie d hp ⟨φ⟩
  | sporadic s => exact hSpor s ⟨φ⟩

theorem kFactThreeSevenTwoGe5_of_forall_goal
    (h : ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K E S : Subgroup X),
      K372Setting X p K E S → K372Goal p K S) :
    KFactThreeSevenTwoGe5 := by
  intro X _ _ hcat p hp hp5 K E S hK hq hc hE hEc h23 hG hKG hS hSN hSC
  exact h X p K E S ⟨hcat, hp, hp5, hK, hq, hc, hE, hEc, h23, hG, hKG, hS, hSN⟩ hSC

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
