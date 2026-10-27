module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def normClass {G : Type} [Group G] (E : Subgroup G) (x : G) : Set G :=
  {y | ∃ n ∈ normalizer (E : Set G), n * x * n⁻¹ = y}

structure M24Out (G : Type) [Group G] (E : Subgroup G) (t : G) : Prop where
  card_E : Nat.card E = 2 ^ 11
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  centralizer_eq : centralizer (E : Set G) = E
  quotient : Nonempty (↥(normalizer (E : Set G)) ⧸ E.subgroupOf (normalizer (E : Set G)) ≃*
    Carrier .M24)
  t_mem : t ∈ E
  t_ne_one : t ≠ 1
  ncard_t : (normClass E t).ncard = 276
  rest : ∃ y ∈ E, y ≠ 1 ∧ y ∉ normClass E t ∧ (normClass E y).ncard = 1771 ∧
    ∀ w ∈ E, w ≠ 1 → w ∉ normClass E t → w ∈ normClass E y

@[expose] def Stage44' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .Fi22 → ∀ {t : G}, (center L).map L.subtype = zpowers t →
      centralizer ({t} : Set G) ≠ L → ∃ E : Subgroup G, E ≤ L ∧ M24Out G E t

end CFSG.EvenSporadicStandard.TwoFi22.DS81
