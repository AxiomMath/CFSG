module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open

structure K37Setting (X : Type) [Group X] [Finite X] (K E S : Subgroup X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  normal : K.Normal
  quasi : CFSG.IsQuasisimple ↥K
  core : CFSG.pPrimeCore 3 ↥K = ⊥
  elem : IsElemAbelian 3 E
  card : Nat.card E = 9
  rank23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
    pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3
  rank_gamma : pRank 3 (rankThreeGamma 1 3 E) ≤ 3
  not_le : ¬ K ≤ rankThreeGamma 1 3 E
  two : IsPGroup 2 S
  le_normalizer : rankThreeGamma 1 3 E ≤ Subgroup.normalizer (S : Set X)

@[expose] def K37Concl {X : Type} [Group X] (K S : Subgroup X) : Prop :=
  (CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥K ∧ ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (S : Set X)) → r = 2 ∨ r = 3) ∨
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA11Type ↥K

@[expose] def K37Goal {X : Type} [Group X] (K S : Subgroup X) : Prop :=
  ¬ S ≤ Subgroup.centralizer (K : Set X) → K37Concl K S

theorem K37Setting.goal_of_catalog {X : Type} [Group X] [Finite X] {K E S : Subgroup X}
    (h : K37Setting X K E S)
    (hLie : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → K37Goal K S)
    (hLie3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → K37Goal K S)
    (hAlt : ∀ n : ℕ, 5 ≤ n → Nonempty (↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) →
      K37Goal K S)
    (hSpor : ∀ s : TauCeti.SporadicName,
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
        K37Goal K S) :
    K37Goal K S := by
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
    by_cases h3 : d.1.characteristic = 3
    · exact hLie3 d h3 ⟨φ⟩
    · exact hLie d h3 ⟨φ⟩
  | sporadic s => exact hSpor s ⟨φ⟩

theorem kFactThreeSevenTwoThree_of_forall_goal
    (h : ∀ (X : Type) [Group X] [Finite X] (K E S : Subgroup X), K37Setting X K E S →
      K37Goal K S) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeSevenTwoThree := by
  intro X _ _ hcat K E S hK hq hc hE hE9 h23 hG hKG hS hSN hSC
  exact h X K E S ⟨hcat, hK, hq, hc, hE, hE9, h23, hG, hKG, hS, hSN⟩ hSC

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
