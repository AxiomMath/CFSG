module

public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction
open scoped MatrixGroups

@[expose] def a2PairRoot {τ : Tag} (α β : Fin τ.rank → ℤ) (i j : Fin 3) : Fin τ.rank → ℤ :=
  ![α + β, β, 0] i - ![α + β, β, 0] j

@[expose] def a2PairRoots {τ : Tag} (α β : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {α, β, α + β, -α, -β, -(α + β)}

private lemma a2PairRoot_add {τ : Tag} (α β : Fin τ.rank → ℤ) (i j l : Fin 3) :
    a2PairRoot α β i j + a2PairRoot α β j l = a2PairRoot α β i l := by
  simp only [a2PairRoot]
  abel

private lemma oddDerivPair_facts {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) :
    IsRoot τ a ∧ IsRoot τ b ∧ a ≠ b ∧ a ≠ -b ∧ IsRoot τ (a + b) ∧
      ¬ IsRoot τ (a - b) ∧ ¬ IsRoot τ ((2 : ℕ) • a + b) ∧
      ¬ IsRoot τ (a + (2 : ℕ) • b) := by
  have hb := (oddDerivPairB_iff (τ := τ) (a := a) (b := b)).2 h
  simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_assoc] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  refine ⟨RootOps.isRootB_iff.1 h1, RootOps.isRootB_iff.1 h2, ?_, ?_,
    RootOps.isRootB_iff.1 h5, ?_, ?_, ?_⟩
  · intro e
    rw [CFSG.LieType.Ree.vecBEq_iff.2 e] at h3
    exact Bool.false_ne_true h3.symm
  · intro e
    rw [CFSG.LieType.Ree.vecBEq_iff.2 e] at h4
    exact Bool.false_ne_true h4.symm
  · intro hr
    rw [RootOps.isRootB_iff.2 hr] at h6
    exact Bool.false_ne_true h6.symm
  · intro hr
    rw [RootOps.isRootB_iff.2 hr] at h7
    exact Bool.false_ne_true h7.symm
  · intro hr
    rw [RootOps.isRootB_iff.2 hr] at h8
    exact Bool.false_ne_true h8.symm

private lemma not_isRoot_two_nsmul {τ : Tag} {γ : Fin τ.rank → ℤ} :
    ¬ IsRoot τ ((2 : ℕ) • γ) := by
  intro h
  exact absurd (eq_one_of_isRoot_nsmul h) (by norm_num)

private lemma two_nsmul_ne_zero {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : γ ≠ 0) :
    (2 : ℕ) • γ ≠ 0 := by
  intro h
  exact hγ (two_nsmul_eq_zero.mp h)

private lemma nonroot_and_ne_zero_of_eq {τ : Tag} {v w : Fin τ.rank → ℤ}
    (h : ¬ IsRoot τ w) (hz : w ≠ 0) (e : v = w) : ¬ IsRoot τ v ∧ v ≠ 0 := by
  rw [e]
  exact ⟨h, hz⟩

private lemma nonroot_and_ne_zero_of_eq_neg {τ : Tag} {v w : Fin τ.rank → ℤ}
    (h : ¬ IsRoot τ w) (hz : w ≠ 0) (e : v = -w) : ¬ IsRoot τ v ∧ v ≠ 0 := by
  rw [e]
  exact ⟨fun hr => h (isRoot_neg_iff.1 hr), by simpa using hz⟩

private lemma isRootB_eq_false {τ : Tag} {v : Fin τ.rank → ℤ}
    (h : ¬ IsRoot τ v) :
    RootOps.isRootB τ v = false := by
  cases hb : RootOps.isRootB τ v with
  | false => rfl
  | true => exact absurd (RootOps.isRootB_iff.1 hb) h

private lemma vecBEq_eq_false {τ : Tag} {u v : Fin τ.rank → ℤ}
    (h : u ≠ v) :
    CFSG.LieType.Ree.vecBEq u v = false := by
  cases hb : CFSG.LieType.Ree.vecBEq u v with
  | false => rfl
  | true => exact absurd (CFSG.LieType.Ree.vecBEq_iff.1 hb) h

private lemma oddDerivPair_of_facts {τ : Tag} {a b : Fin τ.rank → ℤ}
    (ha : IsRoot τ a) (hb : IsRoot τ b) (hne : a ≠ b) (hne' : a ≠ -b)
    (hab : IsRoot τ (a + b)) (hd1 : ¬ IsRoot τ (a - b))
    (hd2 : ¬ IsRoot τ ((2 : ℕ) • a + b)) (hd3 : ¬ IsRoot τ (a + (2 : ℕ) • b)) :
    OddDerivPair τ a b := by
  rw [← oddDerivPairB_iff]
  simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, RootOps.isRootB_iff,
    and_assoc]
  refine ⟨ha, hb, ?_, ?_, hab, ?_, ?_, ?_⟩
  · exact vecBEq_eq_false hne
  · exact vecBEq_eq_false hne'
  · exact isRootB_eq_false hd1
  · exact isRootB_eq_false hd2
  · exact isRootB_eq_false hd3

private lemma oddDerivPair_neg_neg {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) : OddDerivPair τ (-b) (-a) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts (IsRoot.neg hb) (IsRoot.neg ha) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun e => hne (neg_injective e).symm
  · exact fun e => hne' (by simpa using e.symm)
  · convert IsRoot.neg hab using 2
    abel
  · convert hd1 using 2
    abel
  · have h : (2 : ℕ) • (-b) + (-a) = -(a + (2 : ℕ) • b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd3
  · have h : -b + (2 : ℕ) • (-a) = -((2 : ℕ) • a + b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd2

private lemma oddDerivPair_add_neg {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) (h2b : ¬ IsRoot τ ((2 : ℕ) • b)) :
    OddDerivPair τ (a + b) (-b) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts hab (IsRoot.neg hb) ?_ ?_ ?_ ?_ ?_ ?_
  · intro hEq
    apply h2b
    have hsum : a + (2 : ℕ) • b = 0 := by
      calc a + (2 : ℕ) • b = (a + b) + b := by abel
        _ = -b + b := by rw [hEq]
        _ = 0 := by abel
    have h2 : (2 : ℕ) • b = -a := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum
    rw [h2]
    exact IsRoot.neg ha
  · intro hEq
    apply ha.ne_zero
    have h2 : a = 0 := by
      have := congrArg (fun v => v - b) hEq
      simpa [add_sub_cancel_right] using this
    exact h2
  · convert ha using 2
    abel
  · convert hd3 using 2
    abel
  · convert hd2 using 2
    abel
  · convert hd1 using 2
    abel

private lemma oddDerivPair_neg_add {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) (h2a : ¬ IsRoot τ ((2 : ℕ) • a)) :
    OddDerivPair τ (-a) (a + b) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts (IsRoot.neg ha) hab ?_ ?_ ?_ ?_ ?_ ?_
  · intro e
    apply h2a
    have hsum : (2 : ℕ) • a + b = 0 := by
      calc (2 : ℕ) • a + b = (a + b) + a := by abel
        _ = -a + a := by rw [← e]
        _ = 0 := by abel
    have h2 : (2 : ℕ) • a = -b := by
      rw [eq_neg_iff_add_eq_zero]
      exact hsum
    rw [h2]
    exact IsRoot.neg hb
  · intro e
    apply hb.ne_zero
    have h2 : b = 0 := by
      have h1 : a = a + b := neg_injective e
      have := congrArg (fun v => v - a) h1
      simpa using this.symm
    exact h2
  · convert hb using 2
    abel
  · have h : -a - (a + b) = -((2 : ℕ) • a + b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd2
  · have h : (2 : ℕ) • (-a) + (a + b) = -(a - b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd1
  · convert hd3 using 2
    abel

private lemma oddDerivPair_add_neg_right {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) (h2b : ¬ IsRoot τ ((2 : ℕ) • b)) :
    OddDerivPair τ b (-(a + b)) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts hb (IsRoot.neg hab) ?_ ?_ ?_ ?_ ?_ ?_
  · intro e
    apply h2b
    have h1 : a + b = -b := by
      have := congrArg Neg.neg e.symm
      simpa using this
    have hsum : a + (2 : ℕ) • b = 0 := by
      calc a + (2 : ℕ) • b = (a + b) + b := by abel
        _ = -b + b := by rw [h1]
        _ = 0 := by abel
    have h2 : (2 : ℕ) • b = -a := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum
    rw [h2]
    exact IsRoot.neg ha
  · intro e
    apply ha.ne_zero
    have h2 : a = 0 := by
      have := congrArg (fun v => v - b) e
      simpa using this.symm
    exact h2
  · convert IsRoot.neg ha using 2
    abel
  · convert hd3 using 2
    abel
  · have h : (2 : ℕ) • b + -(a + b) = -(a - b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd1
  · have h : b + (2 : ℕ) • (-(a + b)) = -((2 : ℕ) • a + b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd2

private lemma oddDerivPair_neg_add_right {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) (h2a : ¬ IsRoot τ ((2 : ℕ) • a)) :
    OddDerivPair τ (-(a + b)) a := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts (IsRoot.neg hab) ha ?_ ?_ ?_ ?_ ?_ ?_
  · intro e
    apply h2a
    have h1 : a + b = -a := by
      have := congrArg Neg.neg e.symm
      simpa using this.symm
    have hsum : (2 : ℕ) • a + b = 0 := by
      calc (2 : ℕ) • a + b = a + (a + b) := by abel
        _ = a + -a := by rw [h1]
        _ = 0 := by abel
    have h2 : (2 : ℕ) • a = -b := by
      rw [eq_neg_iff_add_eq_zero]
      exact hsum
    rw [h2]
    exact IsRoot.neg hb
  · intro e
    apply hb.ne_zero
    have h2 : b = 0 := by
      have := congrArg (fun v => v + b) e
      simpa using this
    exact h2
  · convert IsRoot.neg hb using 2
    abel
  · have h : -(a + b) - a = -((2 : ℕ) • a + b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd2
  · have h : (2 : ℕ) • (-(a + b)) + a = -(a + (2 : ℕ) • b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd3
  · convert hd1 using 2
    abel

private lemma oddDerivPair_symm {τ : Tag} {a b : Fin τ.rank → ℤ}
    (h : OddDerivPair τ a b) : OddDerivPair τ b a := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  refine oddDerivPair_of_facts hb ha (Ne.symm hne) ?_ ?_ ?_ ?_ ?_
  · intro e
    apply hne'
    rw [e, neg_neg]
  · simpa [add_comm] using hab
  · have h : b - a = -(a - b) := by abel
    rw [h, isRoot_neg_iff]
    exact hd1
  · convert hd3 using 2
    abel
  · convert hd2 using 2
    abel

private lemma oddDerivPair_a2PairRoot_adjacent {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    ∀ i j l : Fin 3, i ≠ j → j ≠ l → i ≠ l →
      OddDerivPair τ (a2PairRoot α β i j) (a2PairRoot α β j l) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  have h2a : ¬ IsRoot τ ((2 : ℕ) • α) := not_isRoot_two_nsmul (γ := α)
  have h2b : ¬ IsRoot τ ((2 : ℕ) • β) := not_isRoot_two_nsmul (γ := β)
  have e2 : OddDerivPair τ (α + β) (-β) := by
    convert oddDerivPair_add_neg h h2b using 2
  have e3 : OddDerivPair τ (-α) (α + β) := by
    convert oddDerivPair_neg_add h h2a using 2
  have e4 : OddDerivPair τ β (-(α + β)) := by
    convert oddDerivPair_add_neg_right h h2b using 2
  have e5 : OddDerivPair τ (-(α + β)) α := by
    convert oddDerivPair_neg_add_right h h2a using 2
  have e6 : OddDerivPair τ (-β) (-α) := oddDerivPair_neg_neg h
  intro i j l hij hjl hil
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp_all [a2PairRoot, add_comm]

private lemma isRoot_a2PairRoot {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) : ∀ i j : Fin 3, i ≠ j → IsRoot τ (a2PairRoot α β i j) := by
  obtain ⟨ha, hb, hne, hne', hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [a2PairRoot] <;>
    first
    | exact ha
    | exact hb
    | exact hab
    | exact IsRoot.neg ha
    | exact IsRoot.neg hb
    | convert IsRoot.neg hab using 2
      abel

private lemma a2PairRoot_facts {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    (¬ IsRoot τ ((2 : ℕ) • α + β) ∧ (2 : ℕ) • α + β ≠ 0) ∧
      (¬ IsRoot τ (α + (2 : ℕ) • β) ∧ α + (2 : ℕ) • β ≠ 0) ∧
      ¬ IsRoot τ (α - β) ∧ α - β ≠ 0 := by
  obtain ⟨ha, hb, hne, -, hab, hd1, hd2, hd3⟩ := oddDerivPair_facts h
  have h2a : ¬ IsRoot τ ((2 : ℕ) • α) := not_isRoot_two_nsmul (γ := α)
  have h2b : ¬ IsRoot τ ((2 : ℕ) • β) := not_isRoot_two_nsmul (γ := β)
  have hz2ab : (2 : ℕ) • α + β ≠ 0 := by
    intro e
    apply h2a
    have : (2 : ℕ) • α = -β := by
      rw [eq_neg_iff_add_eq_zero]
      exact e
    rw [this]
    exact IsRoot.neg hb
  have hza2b : α + (2 : ℕ) • β ≠ 0 := by
    intro e
    apply h2b
    have : (2 : ℕ) • β = -α := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact e
    rw [this]
    exact IsRoot.neg ha
  have hzd : α - β ≠ 0 := by
    intro e
    apply hne
    have := congrArg (fun v => v + β) e
    simpa using this
  exact ⟨⟨hd2, hz2ab⟩, ⟨hd3, hza2b⟩, hd1, hzd⟩

private lemma a2PairRoot_add_self {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    ∀ i j : Fin 3, i ≠ j →
      ¬ IsRoot τ (a2PairRoot α β i j + a2PairRoot α β i j) ∧
        a2PairRoot α β i j + a2PairRoot α β i j ≠ 0 := by
  intro i j hij
  have hr := isRoot_a2PairRoot h i j hij
  have e : a2PairRoot α β i j + a2PairRoot α β i j = (2 : ℕ) • a2PairRoot α β i j := by
    rw [two_smul]
  rw [e]
  exact ⟨not_isRoot_two_nsmul, two_nsmul_ne_zero hr.ne_zero⟩

private lemma a2PairRoot_add_left {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
      ¬ IsRoot τ (a2PairRoot α β i j + a2PairRoot α β i l) ∧
        a2PairRoot α β i j + a2PairRoot α β i l ≠ 0 := by
  obtain ⟨⟨hd2, hz2ab⟩, ⟨hd3, hza2b⟩, hd1, hzd⟩ := a2PairRoot_facts h
  intro i j l hij hil hjl
  fin_cases i
  · fin_cases j <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq hd2 hz2ab (by ring)
  · fin_cases j <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq_neg hd1 hzd (by ring)
  · fin_cases j <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq_neg hd3 hza2b (by ring)

private lemma a2PairRoot_add_right {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    ∀ i j l : Fin 3, i ≠ j → l ≠ j → i ≠ l →
      ¬ IsRoot τ (a2PairRoot α β i j + a2PairRoot α β l j) ∧
        a2PairRoot α β i j + a2PairRoot α β l j ≠ 0 := by
  obtain ⟨⟨hd2, hz2ab⟩, ⟨hd3, hza2b⟩, hd1, hzd⟩ := a2PairRoot_facts h
  intro i j l hij hlj hil
  fin_cases j
  · fin_cases i <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq_neg hd2 hz2ab (by ring)
  · fin_cases i <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq hd1 hzd (by ring)
  · fin_cases i <;> fin_cases l <;> simp_all [a2PairRoot]
    all_goals exact nonroot_and_ne_zero_of_eq hd3 hza2b (by ring)

private lemma fin3_eq_of_ne_ne (i j k l : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hli : l ≠ i) (hlk : l ≠ k) : l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

private lemma a2PairRoot_far {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) :
    ∀ i j k l : Fin 3, i ≠ j → k ≠ l → j ≠ k → i ≠ l →
      ¬ IsRoot τ (a2PairRoot α β i j + a2PairRoot α β k l) ∧
        a2PairRoot α β i j + a2PairRoot α β k l ≠ 0 := by
  intro i j k l hij hkl hjk hil
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      exact a2PairRoot_add_self h i j hij
    · exact a2PairRoot_add_left h i j l hij hil (Ne.symm hlj)
  · have hlj : l = j := fin3_eq_of_ne_ne i j k l hij (Ne.symm hki) hjk (Ne.symm hil) (Ne.symm hkl)
    subst l
    exact a2PairRoot_add_right h i j k hij hjk.symm (Ne.symm hki)

theorem exists_a2Hom_of_oddDerivPair
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {K : Type} [Field K] [Finite K] (ι : K →+* L)
    {α β : Fin τ.rank → ℤ} (h : OddDerivPair τ α β) :
    ∃ ρ : SL(3, K) →* ModGL τ L, ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      ρ (Matrix.SpecialLinearGroup.transvection hij c) =
        pinnedX τ L (a2PairRoot α β i j) (ι c) := by
  let x : Fin 3 → Fin 3 → K → ModGL τ L :=
    fun i j c => pinnedX τ L (a2PairRoot α β i j) (ι c)
  have hx : CFSG.DesarguesianPlanes.IsSteinbergFamily x := by
    refine ⟨?_, ?_⟩
    · intro i j hij c d
      simp only [x, map_add, pinnedX_add]
    · intro i j k l hij hkl hex c d
      have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
      simp only [x]
      by_cases hjk : j = k
      · subst k
        have hil : i ≠ l := fun e => hex ⟨rfl, e.symm⟩
        have hpair := oddDerivPair_a2PairRoot_adjacent h i j l hij hkl hil
        rw [if_pos rfl, commutatorElement_pinnedX_of_oddDerivPair h2 hpair, map_mul]
        congr 1
        exact a2PairRoot_add α β i j l
      · by_cases hil : i = l
        · subst l
          have hkj : k ≠ j := fun e => hjk e.symm
          have hpair : OddDerivPair τ (a2PairRoot α β i j) (a2PairRoot α β k i) :=
            oddDerivPair_symm (oddDerivPair_a2PairRoot_adjacent h k i j hkl hij hkj)
          rw [if_neg hjk, if_pos rfl,
            commutatorElement_pinnedX_of_oddDerivPair h2 hpair, map_neg, CharTwo.neg_eq, map_mul]
          congr 1
          rw [add_comm]
          exact a2PairRoot_add α β k i j
        · have hfar := a2PairRoot_far h i j k l hij hkl hjk hil
          have hne' : a2PairRoot α β i j ≠ -a2PairRoot α β k l := by
            intro e
            exact hfar.2 (by rw [e, neg_add_cancel])
          rw [if_neg hjk, if_neg hil]
          exact commutatorElement_eq_one_iff_commute.2
            (commute_pinnedX_of_oddDeriv (isRoot_a2PairRoot h i j hij)
              (isRoot_a2PairRoot h k l hkl) hne' hfar.1 (ι c) (ι d))
  obtain ⟨ρ, hρ⟩ := CFSG.DesarguesianPlanes.exists_hom_of_steinbergFamily (F := K) hx
  refine ⟨ρ, ?_⟩
  intro i j hij c
  simpa [x] using hρ i j c (Matrix.SpecialLinearGroup.transvection hij c) hij rfl

end CFSG.HardMathSupport.C14Idx
