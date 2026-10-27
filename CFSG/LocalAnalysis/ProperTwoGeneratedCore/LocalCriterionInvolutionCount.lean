module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountIdentities
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountTwoCycles

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev fullFlipSet (u : G) (a b : Ω) : Set G :=
  {v | v ∈ fullClass u ∧ rightAct a v = b}

def classFlipPairSetEquiv (u : G) (a b : Ω) :
    classFlipPair u a b ≃ fullFlipSet u a b where
  toFun v := ⟨v.val.val, v.val.property, v.property⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def classTwoCycleSetEquiv (u : G) (p : Sym2 Ω) :
    classTwoCycle u p ≃ {v : G // v ∈ fullClass u ∧ isTwoCycle v p} where
  toFun v := ⟨v.val.val, v.val.property, v.property⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite G] [Finite Ω]

theorem doubly_transitive_involution_fixed_pair_cycle_count
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (hn : 2 ≤ Nat.card Ω) (u : G) (hu : orderOf u = 2)
    (hk : 2 ≤ Nat.card (fixedSet (Ω := Ω) u))
    (hcentralizer : ∀ a b c d : Ω,
      a ∈ fixedSet u → b ∈ fixedSet u → c ∈ fixedSet u → d ∈ fixedSet u →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (ha : a ∈ fixedSet u) (hb : b ∈ fixedSet u) (hab : a ≠ b) :
    let U := fullClass u
    let F := fixedSet (Ω := Ω) u
    let D := rightStabilizer a ⊓ rightStabilizer b
    let flips := fullFlipSet u a b
    let n := Nat.card Ω
    let k := Nat.card F
    let e := Nat.card flips
    2 ≤ k ∧ U ∩ (D : Set G) = conjugacyWithin D u ∧
      (∀ v ∈ flips, rightAct a v = b ∧ rightAct b v = a) ∧
      (∀ p : Sym2 Ω, ¬ p.IsDiag →
        Nat.card {v : G // v ∈ U ∧ isTwoCycle v p} = e) ∧
      Nat.card U * k * (k - 1) =
        n * (n - 1) * (Subgroup.centralizer ({u} : Set G)).relIndex D ∧
      Nat.card U * (n - k) = n * (n - 1) * e ∧
      (n : ℚ) - k = (k : ℚ) * ((k : ℚ) - 1) * e /
        (Subgroup.centralizer ({u} : Set G)).relIndex D := by
  have he : Nat.card (classFlipPair u a b) = Nat.card (fullFlipSet u a b) :=
    Nat.card_congr (classFlipPairSetEquiv u a b)
  refine ⟨hk, pair_stabilizer_class_intersection u hcentralizer a b ha hb hab,
    ?_, ?_, fixed_pair_class_count hdouble u hcentralizer a b ha hb hab, ?_, ?_⟩
  · intro v hv
    exact ⟨hv.2, class_flip_reverse u hu a b ⟨⟨v, hv.1⟩, hv.2⟩⟩
  · intro p hp
    calc
      _ = Nat.card (classTwoCycle u p) := (Nat.card_congr (classTwoCycleSetEquiv u p)).symm
      _ = Nat.card (classFlipPair u a b) := unordered_pair_two_cycle_count hdouble u hu a b hab p hp
      _ = _ := he
  · simpa only [← he] using moving_class_count hdouble u a b hab
  · simpa only [← he] using
      fixed_pair_degree_rational hdouble u hcentralizer a b ha hb hab hn

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
