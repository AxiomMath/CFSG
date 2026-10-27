module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountConjugation

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

def isTwoCycle (v : G) (p : Sym2 Ω) : Prop :=
  ∃ a b : Ω, a ≠ b ∧ Sym2.mk a b = p ∧
    rightAct a v = b ∧ rightAct b v = a

abbrev classTwoCycle (u : G) (p : Sym2 Ω) : Type _ :=
  {v : fullClass u // isTwoCycle (v : G) p}

theorem isTwoCycle_mk_iff (v : G) (a b : Ω) (hab : a ≠ b) :
    isTwoCycle v (Sym2.mk a b) ↔
      rightAct a v = b ∧ rightAct b v = a := by
  constructor
  · rintro ⟨c, d, _, heq, hc, hd⟩
    rcases (Sym2.mk_eq_mk_iff (p := (c, d)) (q := (a, b))).mp heq with heq | heq
    · have hca : c = a := congrArg Prod.fst heq
      have hdb : d = b := congrArg Prod.snd heq
      simpa only [hca, hdb] using And.intro hc hd
    · have hcb : c = b := congrArg Prod.fst heq
      have hda : d = a := congrArg Prod.snd heq
      simpa only [hcb, hda] using And.intro hd hc
  · intro h
    exact ⟨a, b, hab, rfl, h.1, h.2⟩

def classTwoCycleFlipEquiv (u : G) (hu : orderOf u = 2)
    (a b : Ω) (hab : a ≠ b) :
    classTwoCycle u (Sym2.mk a b) ≃ classFlipPair u a b where
  toFun v := ⟨v.val, ((isTwoCycle_mk_iff (v.val : G) a b hab).mp v.property).1⟩
  invFun v := ⟨v.val, (isTwoCycle_mk_iff (v.val : G) a b hab).mpr
    ⟨v.property, class_flip_reverse u hu a b v⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unordered_pair_two_cycle_count [Finite G]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (u : G) (hu : orderOf u = 2) (a b : Ω) (hab : a ≠ b)
    (p : Sym2 Ω) (hp : ¬ p.IsDiag) :
    Nat.card (classTwoCycle u p) = Nat.card (classFlipPair u a b) := by
  obtain ⟨⟨c, d⟩, rfl⟩ := Sym2.mk_surjective p
  have hcd : c ≠ d := by
    intro heq
    exact hp (Sym2.mk_isDiag_iff.mpr heq)
  calc
    _ = Nat.card (classFlipPair u c d) :=
      Nat.card_congr (classTwoCycleFlipEquiv u hu c d hcd)
    _ = _ := classFlipPair_card_eq_of_doubly_transitive hdouble u c d a b hcd hab

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
