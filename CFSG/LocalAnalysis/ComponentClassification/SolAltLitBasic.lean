module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.AlternatingUnbalancedDegree

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

section Degree

variable {X : Type*} [Group X] [Finite X]

theorem le_two_mul_card_of_isAltTwoComponent {t : X} {K : Subgroup X} {n : ℕ}
    (h : IsAltTwoComponent t K n) : n ≤ 2 * Nat.card X := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := h
  have hX : 0 < Nat.card X := Nat.card_pos
  rcases Nat.lt_or_ge n 2 with hn | hn
  · omega
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have h1 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
        Fintype.card_fin]
    have h2 : Nat.card (K ⧸ pPrimeCore 2 K) = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr e.toEquiv
    have h3 : Nat.card (K ⧸ pPrimeCore 2 K) ≤ Nat.card K :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (pPrimeCore 2 K))
    have h4 : Nat.card K ≤ Nat.card X := K.card_le_card_group
    have h5 : n ≤ n.factorial := Nat.self_le_factorial n
    omega

theorem exists_isAltTwoComponent_max_odd
    (h : ∃ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n ∧ Odd n ∧ 9 ≤ n) :
    ∃ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n ∧ Odd n ∧ 9 ≤ n ∧
      ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' ≤ n := by
  classical
  let P : ℕ → Prop := fun n =>
    Odd n ∧ 9 ≤ n ∧ ∃ (t : X) (K : Subgroup X), IsAltTwoComponent t K n
  obtain ⟨t₀, K₀, n₀, h₀, ho₀, h9₀⟩ := h
  obtain ⟨hoN, h9N, t, K, hK⟩ : P (Nat.findGreatest P (2 * Nat.card X)) :=
    Nat.findGreatest_spec (le_two_mul_card_of_isAltTwoComponent h₀) ⟨ho₀, h9₀, t₀, K₀, h₀⟩
  refine ⟨t, K, _, hK, hoN, h9N, fun t' K' n' h' ho' => ?_⟩
  by_cases h9' : 9 ≤ n'
  · exact Nat.le_findGreatest (le_two_mul_card_of_isAltTwoComponent h') ⟨ho', h9', t', K', h'⟩
  · omega

theorem exists_isAltTwoComponent_max
    (h : ∃ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n ∧ 8 ≤ n) :
    ∃ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n ∧ 8 ≤ n ∧
      ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → n' ≤ n := by
  classical
  let P : ℕ → Prop := fun n => 8 ≤ n ∧ ∃ (t : X) (K : Subgroup X), IsAltTwoComponent t K n
  obtain ⟨t₀, K₀, n₀, h₀, h8₀⟩ := h
  obtain ⟨h8N, t, K, hK⟩ : P (Nat.findGreatest P (2 * Nat.card X)) :=
    Nat.findGreatest_spec (le_two_mul_card_of_isAltTwoComponent h₀) ⟨h8₀, t₀, K₀, h₀⟩
  refine ⟨t, K, _, hK, h8N, fun t' K' n' h' => ?_⟩
  by_cases h8' : 8 ≤ n'
  · exact Nat.le_findGreatest (le_two_mul_card_of_isAltTwoComponent h') ⟨h8', t', K', h'⟩
  · omega

end Degree

theorem uOutcome_of_mulEquiv_alternating {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {m : ℕ} (hm : 7 ≤ m) (e : X ≃* alternatingGroup (Fin m))
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) :
    OutcomeLocal.UOutcome X := by
  let eF : GeneralizedFitting.subgroup X ≃* X := GSLit.generalizedFittingEquivOfSimple
  have : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  obtain ⟨z, hz2, hzc⟩ := hz
  obtain ⟨hodd, h1, -⟩ := AlternatingUnbalanced.alternating_generalized_fitting_unbalanced_degree
    hFnonab hm ⟨eF.trans e⟩ hz2 hzc
  have hm1 : m % 4 ≠ 1 := fun h => (h1 h).ne GSLit.generalizedFitting_eq_top_of_simple
  exact Or.inr (Or.inl ⟨m, hodd, hm, ⟨eF.trans e⟩, fun h => absurd h hm1⟩)

end CFSG.ComponentClassification.SolAltLit
