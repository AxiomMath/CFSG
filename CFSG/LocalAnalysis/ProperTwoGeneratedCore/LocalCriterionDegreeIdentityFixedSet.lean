module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction Gᵐᵒᵖ Ω]

theorem full_fixed_set_odd [Finite Ω] (u : G) (hu : orderOf u = 2)
    (hodd : Odd (Nat.card Ω)) :
    Odd (Nat.card (fixedSet (Ω := Ω) u)) := by
  classical
  let := Fintype.ofFinite Ω
  let := Fintype.ofFinite (fixedSet (Ω := Ω) u)
  let σ : Equiv.Perm Ω := MulAction.toPerm (MulOpposite.op u)
  have hsquare : σ ^ 2 = 1 := by
    have huu : u * u = 1 := by
      simpa only [hu, pow_two] using pow_orderOf_eq_one u
    apply Equiv.ext
    intro x
    change rightAct (rightAct x u) u = x
    rw [rightAct_mul, huu, rightAct_one]
  have hfixed : Fintype.card (fixedSet (Ω := Ω) u) = σ.supportᶜ.card := by
    apply Fintype.card_of_subtype
    intro x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    rfl
  have hcard := Finset.card_compl_add_card σ.support
  rw [← hfixed, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcard
  obtain ⟨movingHalf, hhalf⟩ := (even_iff_two_dvd.mpr
    (Equiv.Perm.two_dvd_card_support hsquare))
  obtain ⟨degreeHalf, hdegree⟩ := hodd
  refine ⟨degreeHalf - movingHalf, ?_⟩
  omega

theorem two_le_full_fixed_set [Finite Ω] (u : G) (a b : Ω)
    (ha : rightAct a u = a) (hb : rightAct b u = b) (hab : a ≠ b) :
    2 ≤ Nat.card (fixedSet (Ω := Ω) u) := by
  let F := fixedSet (Ω := Ω) u
  let := Fintype.ofFinite F
  have htwo : 1 < Fintype.card F := (Fintype.one_lt_card_iff).mpr
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun heq => hab (congrArg Subtype.val heq)⟩
  rw [← Nat.card_eq_fintype_card] at htwo
  change 2 ≤ Nat.card F
  omega

theorem full_fixed_set_card_lt_of_faithful [Finite Ω]
    (hfaithful : ∀ g : G, (∀ x : Ω, rightAct x g = x) → g = 1)
    (u : G) (hu : orderOf u = 2) :
    Nat.card (fixedSet (Ω := Ω) u) < Nat.card Ω := by
  classical
  have hune : u ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hu
    norm_num at hu
  have hmoved : ∃ x : Ω, rightAct x u ≠ x := by
    by_contra hnone
    have hall : ∀ x : Ω, rightAct x u = x := by
      simpa only [not_exists, not_not] using hnone
    exact hune (hfaithful u hall)
  obtain ⟨x, hx⟩ := hmoved
  let := Fintype.ofFinite Ω
  let := Fintype.ofFinite (fixedSet (Ω := Ω) u)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_of_notMem (b := x)
    (fun y : fixedSet (Ω := Ω) u => y.val) Subtype.val_injective
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

theorem full_fixed_set_bounds [Finite Ω]
    (hfaithful : ∀ g : G, (∀ x : Ω, rightAct x g = x) → g = 1)
    (hodd : Odd (Nat.card Ω)) (u : G) (hu : orderOf u = 2)
    (a b : Ω) (ha : rightAct a u = a) (hb : rightAct b u = b) (hab : a ≠ b) :
    3 ≤ Nat.card (fixedSet (Ω := Ω) u) ∧
      Nat.card (fixedSet (Ω := Ω) u) < Nat.card Ω ∧
      Odd (Nat.card (fixedSet (Ω := Ω) u)) := by
  have htwo := two_le_full_fixed_set u a b ha hb hab
  have hkodd := full_fixed_set_odd u hu hodd
  refine ⟨?_, full_fixed_set_card_lt_of_faithful hfaithful u hu, hkodd⟩
  obtain ⟨j, hj⟩ := hkodd
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
