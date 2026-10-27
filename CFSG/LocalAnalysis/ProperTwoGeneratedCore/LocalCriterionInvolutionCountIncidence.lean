module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountFusion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev fixedPairIncidence (u : G) : Type _ :=
  Σ v : fullClass u, orderedDistinctPairs (fixedSet (Ω := Ω) (v : G))

def fixedPairProjection (u : G) (x : fixedPairIncidence (Ω := Ω) u) :
    orderedDistinctPairs Ω :=
  ⟨(x.2.val.1.val, x.2.val.2.val), fun h => x.2.property (Subtype.ext h)⟩

def fixedPairProjectionFiberEquiv (u : G) (p : orderedDistinctPairs Ω) :
    {x : fixedPairIncidence u // fixedPairProjection u x = p} ≃
      classFixPair u p.val.1 p.val.2 where
  toFun x := ⟨x.val.1, by
    have hpair := congrArg Subtype.val x.property
    have ha := congrArg Prod.fst hpair
    have hb := congrArg Prod.snd hpair
    exact ⟨ha ▸ x.val.2.val.1.property, hb ▸ x.val.2.val.2.property⟩⟩
  invFun v := ⟨⟨v.val, ⟨(⟨p.val.1, v.property.1⟩, ⟨p.val.2, v.property.2⟩),
    fun h => p.property (congrArg Subtype.val h)⟩⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact (congrArg Prod.fst (congrArg Subtype.val x.property)).symm
      · apply Subtype.ext
        exact (congrArg Prod.snd (congrArg Subtype.val x.property)).symm
  right_inv v := rfl

theorem fixedPairIncidence_card [Finite G] [Finite Ω] (u : G) :
    Nat.card (fixedPairIncidence (Ω := Ω) u) =
      Nat.card (fullClass u) *
        (Nat.card (fixedSet (Ω := Ω) u) * (Nat.card (fixedSet (Ω := Ω) u) - 1)) := by
  classical
  let := Fintype.ofFinite (fullClass u)
  change Nat.card (Σ v : fullClass u, orderedDistinctPairs (fixedSet (Ω := Ω) (v : G))) = _
  rw [Nat.card_sigma]
  simp only [orderedDistinctPairs_card,
    conjugate_fixedSet_card u _ (Subtype.prop _), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem fixedPairIncidence_card_of_double_transitivity [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (a b : Ω) (hab : a ≠ b) :
    Nat.card (fixedPairIncidence (Ω := Ω) u) =
      Nat.card Ω * (Nat.card Ω - 1) * Nat.card (classFixPair u a b) := by
  have hf (p : orderedDistinctPairs Ω) :
      Nat.card {x : fixedPairIncidence u // fixedPairProjection u x = p} =
        Nat.card (classFixPair u a b) :=
    (Nat.card_congr (fixedPairProjectionFiberEquiv u p)).trans
      (classFixPair_card_eq_of_doubly_transitive hdouble u _ _ a b p.property hab)
  rw [card_eq_card_mul_constant_fiber (fixedPairProjection (Ω := Ω) u) _ hf,
    orderedDistinctPairs_card]

abbrev movingIncidence (u : G) : Type _ :=
  Σ v : fullClass u, {a : Ω // rightAct a (v : G) ≠ a}

def movingProjection (u : G) (x : movingIncidence (Ω := Ω) u) : orderedDistinctPairs Ω :=
  ⟨(x.2.val, rightAct x.2.val (x.1 : G)), x.2.property.symm⟩

def movingProjectionFiberEquiv (u : G) (p : orderedDistinctPairs Ω) :
    {x : movingIncidence u // movingProjection u x = p} ≃
      classFlipPair u p.val.1 p.val.2 where
  toFun x := ⟨x.val.1, by
    have hpair := congrArg Subtype.val x.property
    have ha := congrArg Prod.fst hpair
    have hb := congrArg Prod.snd hpair
    exact (congrArg (fun a : Ω => rightAct a (x.val.1 : G)) ha.symm).trans hb⟩
  invFun v := ⟨⟨v.val, ⟨p.val.1, fun h => p.property (h.symm.trans v.property)⟩⟩,
    Subtype.ext (Prod.ext rfl v.property)⟩
  left_inv x := by
    apply Subtype.ext
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (congrArg Prod.fst (congrArg Subtype.val x.property)).symm
  right_inv v := rfl

theorem moving_points_card [Finite Ω] (u : G) :
    Nat.card {a : Ω // rightAct a u ≠ a} = Nat.card Ω - Nat.card (fixedSet (Ω := Ω) u) := by
  classical
  let := Fintype.ofFinite Ω
  change Nat.card {a : Ω // rightAct a u ≠ a} =
    Nat.card Ω - Nat.card {a : Ω // rightAct a u = a}
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_subtype_compl (fun a : Ω => rightAct a u = a)

theorem movingIncidence_card [Finite G] [Finite Ω] (u : G) :
    Nat.card (movingIncidence (Ω := Ω) u) =
      Nat.card (fullClass u) * (Nat.card Ω - Nat.card (fixedSet (Ω := Ω) u)) := by
  classical
  let := Fintype.ofFinite (fullClass u)
  change Nat.card (Σ v : fullClass u, {a : Ω // rightAct a (v : G) ≠ a}) = _
  rw [Nat.card_sigma]
  simp only [moving_points_card, conjugate_fixedSet_card u _ (Subtype.prop _),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem movingIncidence_card_of_double_transitivity [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (a b : Ω) (hab : a ≠ b) :
    Nat.card (movingIncidence (Ω := Ω) u) =
      Nat.card Ω * (Nat.card Ω - 1) * Nat.card (classFlipPair u a b) := by
  have hf (p : orderedDistinctPairs Ω) :
      Nat.card {x : movingIncidence u // movingProjection u x = p} =
        Nat.card (classFlipPair u a b) :=
    (Nat.card_congr (movingProjectionFiberEquiv u p)).trans
      (classFlipPair_card_eq_of_doubly_transitive hdouble u _ _ a b p.property hab)
  rw [card_eq_card_mul_constant_fiber (movingProjection (Ω := Ω) u) _ hf,
    orderedDistinctPairs_card]

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
