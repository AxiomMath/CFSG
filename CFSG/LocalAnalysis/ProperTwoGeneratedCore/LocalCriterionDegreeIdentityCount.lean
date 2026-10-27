module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountIdentities

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction Gᵐᵒᵖ Ω]

theorem full_fixed_pair_rational_class_count [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b) :
    (Nat.card (fullClass u) : ℚ) =
      (Nat.card Ω : ℚ) * (Nat.card Ω - 1) *
        (Subgroup.centralizer ({u} : Set G)).relIndex
          (rightStabilizer a ⊓ rightStabilizer b) /
        ((Nat.card (fixedSet (Ω := Ω) u) : ℚ) *
          (Nat.card (fixedSet (Ω := Ω) u) - 1)) := by
  classical
  let k := Nat.card (fixedSet (Ω := Ω) u)
  let n := Nat.card Ω
  let := Fintype.ofFinite Ω
  let := Fintype.ofFinite (fixedSet (Ω := Ω) u)
  have hk2 : 2 ≤ k := by
    have hcard := Fintype.one_lt_card_iff.mpr
      (show ∃ x y : fixedSet (Ω := Ω) u, x ≠ y from
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩)
    rw [← Nat.card_eq_fintype_card] at hcard
    change 1 < k at hcard
    omega
  have hkn : k ≤ n := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hcount := fixed_pair_class_count hdouble u hcentralizer a b ha hb hab
  change Nat.card (fullClass u) * k * (k - 1) = n * (n - 1) *
    (Subgroup.centralizer ({u} : Set G)).relIndex
      (rightStabilizer a ⊓ rightStabilizer b) at hcount
  have hQ :
      (Nat.card (fullClass u) : ℚ) * k * ((k : ℚ) - 1) =
        (n : ℚ) * ((n : ℚ) - 1) *
          (Subgroup.centralizer ({u} : Set G)).relIndex
            (rightStabilizer a ⊓ rightStabilizer b) := by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hcount
    simpa only [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_sub hn1, Nat.cast_one]
      using hcast
  have hkQ : (2 : ℚ) ≤ k := by exact_mod_cast hk2
  have hdenom : (k : ℚ) * ((k : ℚ) - 1) ≠ 0 := by nlinarith
  change (Nat.card (fullClass u) : ℚ) =
    (n : ℚ) * ((n : ℚ) - 1) *
      (Subgroup.centralizer ({u} : Set G)).relIndex
        (rightStabilizer a ⊓ rightStabilizer b) /
      ((k : ℚ) * ((k : ℚ) - 1))
  apply (eq_div_iff hdenom).mpr
  simpa only [mul_assoc] using hQ

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
