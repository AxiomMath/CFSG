module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountIncidence
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

def classFixPairIntersectionEquiv (u : G) (a b : Ω) :
    classFixPair u a b ≃
      {v : G // v ∈ fullClass u ∩
        ((rightStabilizer a ⊓ rightStabilizer b : Subgroup G) : Set G)} where
  toFun v := ⟨v.val.val, v.val.property,
    (mem_rightStabilizer a _).mpr v.property.1,
    (mem_rightStabilizer b _).mpr v.property.2⟩
  invFun v := ⟨⟨v.val, v.property.1⟩,
    (mem_rightStabilizer a _).mp v.property.2.1,
    (mem_rightStabilizer b _).mp v.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixed_pair_fiber_card_eq_centralizer_index [Finite G] (u : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b) :
    Nat.card (classFixPair u a b) =
      (Subgroup.centralizer ({u} : Set G)).relIndex
        (rightStabilizer a ⊓ rightStabilizer b) := by
  rw [Nat.card_congr (classFixPairIntersectionEquiv u a b)]
  change Nat.card {v : G // v ∈ conjugacyWithin (⊤ : Subgroup G) u ∩
    ((rightStabilizer a ⊓ rightStabilizer b : Subgroup G) : Set G)} = _
  rw [pair_stabilizer_class_intersection u hcentralizer a b ha hb hab,
    conjugacyWithin_card_eq_centralizer_index]
  rfl

theorem fixed_pair_class_count [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b) :
    Nat.card (fullClass u) * Nat.card (fixedSet (Ω := Ω) u) *
        (Nat.card (fixedSet (Ω := Ω) u) - 1) =
      Nat.card Ω * (Nat.card Ω - 1) *
        (Subgroup.centralizer ({u} : Set G)).relIndex
          (rightStabilizer a ⊓ rightStabilizer b) := by
  calc
    _ = Nat.card (fixedPairIncidence (Ω := Ω) u) := by
      rw [fixedPairIncidence_card, mul_assoc]
    _ = Nat.card Ω * (Nat.card Ω - 1) * Nat.card (classFixPair u a b) :=
      fixedPairIncidence_card_of_double_transitivity hdouble u a b hab
    _ = _ := by rw [fixed_pair_fiber_card_eq_centralizer_index u hcentralizer a b ha hb hab]

theorem moving_class_count [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (a b : Ω) (hab : a ≠ b) :
    Nat.card (fullClass u) * (Nat.card Ω - Nat.card (fixedSet (Ω := Ω) u)) =
      Nat.card Ω * (Nat.card Ω - 1) * Nat.card (classFlipPair u a b) := by
  rw [← movingIncidence_card]
  exact movingIncidence_card_of_double_transitivity hdouble u a b hab

theorem pair_centralizer_index_pos [Finite G] (u : G) (a b : Ω) :
    0 < (Subgroup.centralizer ({u} : Set G)).relIndex
      (rightStabilizer a ⊓ rightStabilizer b) := by
  change 0 < ((Subgroup.centralizer ({u} : Set G)).subgroupOf
    (rightStabilizer a ⊓ rightStabilizer b)).index
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem fixed_pair_degree_rational [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b)
    (hn : 2 ≤ Nat.card Ω) :
    ((Nat.card Ω : ℚ) - Nat.card (fixedSet (Ω := Ω) u)) =
      (Nat.card (fixedSet (Ω := Ω) u) : ℚ) *
        (Nat.card (fixedSet (Ω := Ω) u) - 1) * Nat.card (classFlipPair u a b) /
        (Subgroup.centralizer ({u} : Set G)).relIndex
          (rightStabilizer a ⊓ rightStabilizer b) := by
  let k := Nat.card (fixedSet (Ω := Ω) u)
  let n := Nat.card Ω
  let c := (Subgroup.centralizer ({u} : Set G)).relIndex
    (rightStabilizer a ⊓ rightStabilizer b)
  let e := Nat.card (classFlipPair u a b)
  let m := Nat.card (fullClass u)
  have hkn : k ≤ n := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hkpos : 0 < k := by
    have : Nonempty (fixedSet (Ω := Ω) u) := ⟨⟨a, ha⟩⟩
    exact Nat.card_pos
  have hcpos : 0 < c := pair_centralizer_index_pos u a b
  have h1 : m * k * (k - 1) = n * (n - 1) * c :=
    fixed_pair_class_count hdouble u hcentralizer a b ha hb hab
  have h2 : m * (n - k) = n * (n - 1) * e := moving_class_count hdouble u a b hab
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have h1Q : (m : ℚ) * k * ((k : ℚ) - 1) = (n : ℚ) * ((n : ℚ) - 1) * c := by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) h1
    simpa only [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hkpos),
      Nat.cast_sub hn1, Nat.cast_one] using hcast
  have h2Q : (m : ℚ) * ((n : ℚ) - k) = (n : ℚ) * ((n : ℚ) - 1) * e := by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) h2
    simpa only [Nat.cast_mul, Nat.cast_sub hkn, Nat.cast_sub hn1,
      Nat.cast_one] using hcast
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hnQ : 0 < (n : ℚ) * ((n : ℚ) - 1) := by
    have htwo : (2 : ℚ) ≤ n := by exact_mod_cast hn
    nlinarith
  change (n : ℚ) - k = (k : ℚ) * ((k : ℚ) - 1) * e / c
  apply (eq_div_iff hcQ).mpr
  have hproduct := congrArg (fun x : ℚ => x * ((n : ℚ) - k)) h1Q
  rw [show (m : ℚ) * k * ((k : ℚ) - 1) * ((n : ℚ) - k) =
    ((m : ℚ) * ((n : ℚ) - k)) * ((k : ℚ) * ((k : ℚ) - 1)) by ring, h2Q] at hproduct
  apply mul_left_cancel₀ hnQ.ne'
  nlinarith [hproduct]

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
