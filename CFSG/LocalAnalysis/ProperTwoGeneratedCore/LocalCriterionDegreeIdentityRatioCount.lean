module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentitySubstitution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction Gᵐᵒᵖ Ω]

theorem full_swap_orbit_card (u t : G) (a b : Ω)
    (horbit : fullFlipSet u a b =
      conjugacyWithin (rightStabilizer a ⊓ rightStabilizer b) (u * t)) :
    Nat.card (fullFlipSet u a b) =
      (Subgroup.centralizer ({u * t} : Set G)).relIndex
        (rightStabilizer a ⊓ rightStabilizer b) := by
  rw [horbit, conjugacyWithin_card_eq_centralizer_index]
  rfl

theorem full_degree_count_of_derived_swap_orbit [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u t : G)
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b)
    (horbit : fullFlipSet u a b =
      conjugacyWithin (rightStabilizer a ⊓ rightStabilizer b) (u * t)) :
    let D := rightStabilizer a ⊓ rightStabilizer b
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    let C := D ⊓ Subgroup.centralizer (V : Set G)
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let B := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let ratio : ℚ := (C.relIndex A : ℚ) / C.relIndex B
    let n := Nat.card Ω
    let k := Nat.card (fixedSet (Ω := Ω) u)
    (n : ℚ) - k = (k : ℚ) * ((k : ℚ) - 1) * ratio ∧
      (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * ratio + 1) := by
  have hk2 : 2 ≤ Nat.card (fixedSet (Ω := Ω) u) := by
    let := Fintype.ofFinite (fixedSet (Ω := Ω) u)
    have htwo := Fintype.one_lt_card_iff.mpr
      (show ∃ x y : fixedSet (Ω := Ω) u, x ≠ y from
        ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩)
    rw [← Nat.card_eq_fintype_card] at htwo
    omega
  have hkn : Nat.card (fixedSet (Ω := Ω) u) ≤ Nat.card Ω :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hn : 2 ≤ Nat.card Ω := hk2.trans hkn
  have he := full_swap_orbit_card u t a b horbit
  have hpair := fixed_pair_degree_rational hdouble u hcentralizer a b ha hb hab hn
  have hcard := Nat.card_congr (classFlipPairSetEquiv u a b)
  rw [hcard, he] at hpair
  have hratio := generated_centralizer_index_ratio
    (rightStabilizer a ⊓ rightStabilizer b) u t
  have hmove :
      (Nat.card Ω : ℚ) - Nat.card (fixedSet (Ω := Ω) u) =
        (Nat.card (fixedSet (Ω := Ω) u) : ℚ) *
          (Nat.card (fixedSet (Ω := Ω) u) - 1) *
          (((Subgroup.centralizer ({u * t} : Set G)).relIndex
              (rightStabilizer a ⊓ rightStabilizer b) : ℚ) /
            (Subgroup.centralizer ({u} : Set G)).relIndex
              (rightStabilizer a ⊓ rightStabilizer b)) := by
    simpa only [mul_div_assoc] using hpair
  rw [hratio] at hmove
  exact ⟨hmove, degree_identity_of_moving_count _ _ _ hmove⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
