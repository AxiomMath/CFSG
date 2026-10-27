module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

section Heart

variable (d : ℕ)

abbrev PM := Fin d → ZMod 2

@[expose] def evenSub : AddSubgroup (PM d) where
  carrier := {f | ∑ i, f i = 0}
  add_mem' := by
    intro f g hf hg
    show ∑ i, (f + g) i = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [show ∑ i, f i = 0 from hf, show ∑ i, g i = 0 from hg, add_zero]
  zero_mem' := by
    show ∑ i, (0 : PM d) i = 0
    simp
  neg_mem' := by
    intro f hf
    have h : -f = f := funext fun i => ZMod.neg_eq_self_mod_two (f i)
    show ∑ i, (-f) i = 0
    rw [h]
    exact hf

@[expose] def constSub : AddSubgroup (PM d) where
  carrier := {f | ∀ i j, f i = f j}
  add_mem' := by
    intro f g hf hg i j
    show f i + g i = f j + g j
    rw [show f i = f j from hf i j, show g i = g j from hg i j]
  zero_mem' := fun _ _ => rfl
  neg_mem' := by
    intro f hf i j
    show -f i = -f j
    rw [show f i = f j from hf i j]

abbrev Heart := ↥(evenSub d) ⧸ (constSub d).addSubgroupOf (evenSub d)

variable {d}

@[expose] def actPM (σ : Perm (Fin d)) : PM d →+ PM d where
  toFun f := fun i => f (σ⁻¹ i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem actPM_apply (σ : Perm (Fin d)) (f : PM d) (i : Fin d) : actPM σ f i = f (σ⁻¹ i) := rfl

theorem actPM_mem_evenSub (σ : Perm (Fin d)) {f : PM d} (hf : f ∈ evenSub d) :
    actPM σ f ∈ evenSub d := by
  have : ∑ i, f (σ⁻¹ i) = ∑ i, f i := Equiv.sum_comp σ⁻¹ f
  show ∑ i, f (σ⁻¹ i) = 0
  rw [this]; exact hf

theorem actPM_mem_constSub (σ : Perm (Fin d)) {f : PM d} (hf : f ∈ constSub d) :
    actPM σ f ∈ constSub d := fun _ _ => hf _ _

@[expose] def actE (σ : Perm (Fin d)) : ↥(evenSub d) →+ ↥(evenSub d) where
  toFun f := ⟨actPM σ f.1, actPM_mem_evenSub σ f.2⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[expose] def heartAct (σ : Perm (Fin d)) : Heart d →+ Heart d :=
  QuotientAddGroup.map _ _ (actE σ) (by
    intro f hf
    exact actPM_mem_constSub σ hf)

theorem heartAct_mk (σ : Perm (Fin d)) (f : ↥(evenSub d)) :
    heartAct σ (QuotientAddGroup.mk f) = QuotientAddGroup.mk (actE σ f) := rfl

@[expose] def pairVec (x y : Fin d) : PM d := (Pi.single x 1 : PM d) + (Pi.single y 1 : PM d)

theorem pairVec_mem_evenSub (x y : Fin d) : pairVec x y ∈ evenSub d := by
  show ∑ i, pairVec x y i = 0
  simp only [pairVec, Pi.add_apply, Finset.sum_add_distrib]
  simp [Pi.single_apply]
  try decide

@[expose] def pairE (x y : Fin d) : ↥(evenSub d) := ⟨pairVec x y, pairVec_mem_evenSub x y⟩

theorem actE_pairE (σ : Perm (Fin d)) (x y : Fin d) :
    actE σ (pairE x y) = pairE (σ x) (σ y) := by
  apply Subtype.ext
  funext i
  simp only [actE, actPM, pairE, pairVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
    Pi.single_apply]
  have h1 : σ⁻¹ i = x ↔ i = σ x := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have h2 : σ⁻¹ i = y ↔ i = σ y := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  simp only [h1, h2]

theorem exists_second_one {f : PM d} (hf : f ∈ evenSub d) {a : Fin d} (ha : f a = 1) :
    ∃ b, b ≠ a ∧ f b = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ x, x ≠ a → f x = 0 := by
    intro x hx
    have := h x hx
    revert this
    generalize f x = t
    revert t
    decide
  have : ∑ i, f i = 1 := by
    rw [Finset.sum_eq_single a (fun x _ hx => h0 x hx) (by simp), ha]
  have h2 : ∑ i, f i = 0 := hf
  rw [h2] at this
  exact absurd this (by decide)

theorem zmod_two_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

theorem exists_abc {f : ↥(evenSub d)} (hf : (f : PM d) ∉ constSub d) :
    ∃ a b c : Fin d, b ≠ a ∧ f.1 a = 1 ∧ f.1 b = 1 ∧ f.1 c = 0 := by
  have hnc : ∃ i j, f.1 i ≠ f.1 j := by
    by_contra h
    push Not at h
    exact hf (fun i j => h i j)
  obtain ⟨i, j, hij⟩ := hnc
  have key : ∃ a c, f.1 a = 1 ∧ f.1 c = 0 := by
    rcases zmod_two_cases (f.1 i) with hi | hi <;> rcases zmod_two_cases (f.1 j) with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · exact ⟨j, i, hj, hi⟩
    · exact ⟨i, j, hi, hj⟩
    · exact absurd (hi.trans hj.symm) hij
  obtain ⟨a, c, ha, hc⟩ := key
  obtain ⟨b, hb, hb1⟩ := exists_second_one f.2 ha
  exact ⟨a, b, c, hb, ha, hb1, hc⟩


theorem cycle_step {u0 : ↥(evenSub d)} {a b c : Fin d} (hba : b ≠ a) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : u0.1 a = 1) (hb : u0.1 b = 1) (hc : u0.1 c = 0) :
    ∃ σ ∈ alternatingGroup (Fin d), actE σ u0 + u0 = pairE b c := by
  refine ⟨(swap a b * swap b c)⁻¹, ?_, ?_⟩
  · rw [mem_alternatingGroup, map_inv, map_mul, sign_swap hba.symm, sign_swap hbc]
    decide
  · apply Subtype.ext
    funext i
    show u0.1 (((swap a b * swap b c)⁻¹)⁻¹ i) + u0.1 i = pairVec b c i
    rw [inv_inv, Perm.mul_apply]
    by_cases hia : i = a
    · subst hia
      rw [swap_apply_of_ne_of_ne hba.symm hac, swap_apply_left, ha, hb]
      simp [pairVec, hba, hac]
      try decide
    · by_cases hib : i = b
      · subst hib
        rw [swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm, hb, hc]
        simp [pairVec, hbc]
        try decide
      · by_cases hic : i = c
        · subst hic
          rw [swap_apply_right, swap_apply_right, ha, hc]
          simp [pairVec, hbc.symm]
          try decide
        · rw [swap_apply_of_ne_of_ne hib hic, swap_apply_of_ne_of_ne hia hib]
          simp [pairVec, hib, hic]
          rcases zmod_two_cases (u0.1 i) with h | h <;> rw [h] <;> decide

theorem exists_even_pair (hd : 4 ≤ d) {b c x y : Fin d} (hbc : b ≠ c) (hxy : x ≠ y) :
    ∃ σ ∈ alternatingGroup (Fin d), σ b = x ∧ σ c = y := by
  classical
  have hxy1 : x ≠ swap b x c := by
    rw [swap_apply_def]
    split_ifs with h1 h2
    · exact absurd h1 hbc.symm
    · intro h; exact hbc (h.symm.trans h2.symm)
    · exact fun h => h2 h.symm
  have hσ0b : (swap (swap b x c) y * swap b x) b = x := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxy1 hxy]
  have hσ0c : (swap (swap b x c) y * swap b x) c = y := by
    rw [Perm.mul_apply, swap_apply_left]
  by_cases hs : (swap (swap b x c) y * swap b x) ∈ alternatingGroup (Fin d)
  · exact ⟨_, hs, hσ0b, hσ0c⟩
  · obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ ((Finset.univ.erase b).erase c),
        ∃ q ∈ ((Finset.univ.erase b).erase c), p ≠ q := by
      apply Finset.one_lt_card.1
      have h1 : c ∈ Finset.univ.erase b := by simp [hbc.symm]
      rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ b)]
      simp
      omega
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hp hq
    refine ⟨(swap (swap b x c) y * swap b x) * swap p q, ?_, ?_, ?_⟩
    · rw [mem_alternatingGroup] at hs ⊢
      rw [map_mul, sign_swap hpq]
      rcases Int.units_eq_one_or (sign (swap (swap b x c) y * swap b x)) with h | h
      · exact absurd h hs
      · rw [h]; decide
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hp.2) (Ne.symm hq.2), hσ0b]
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hp.1) (Ne.symm hq.1), hσ0c]


theorem pairE_add_self (x y : Fin d) : pairE x y + pairE x y = 0 := by
  apply Subtype.ext
  funext i
  show pairVec x y i + pairVec x y i = 0
  rcases zmod_two_cases (pairVec x y i) with h | h <;> rw [h] <;> decide

theorem mk_mem_of_pairs (U : AddSubgroup (Heart d))
    (hpairs : ∀ x y : Fin d, x ≠ y → (QuotientAddGroup.mk (pairE x y) : Heart d) ∈ U) :
    ∀ f : ↥(evenSub d), (QuotientAddGroup.mk f : Heart d) ∈ U := by
  classical
  intro f
  induction' hn : (Finset.univ.filter fun i => f.1 i = 1).card using Nat.strong_induction_on
    with n ih generalizing f
  by_cases h0 : ∃ a, f.1 a = 1
  · obtain ⟨a, ha⟩ := h0
    obtain ⟨b, hba, hb⟩ := exists_second_one f.2 ha
    set f' : ↥(evenSub d) := f + pairE a b with hf'
    have hf'val : ∀ i, f'.1 i = f.1 i + pairVec a b i := fun i => rfl
    have hfa : f'.1 a = 0 := by
      rw [hf'val, ha]; simp [pairVec, hba.symm]; decide
    have hlt : (Finset.univ.filter fun i => f'.1 i = 1).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_cases hia : i = a
        · subst hia; rw [hfa] at hi; exact absurd hi (by decide)
        · by_cases hib : i = b
          · subst hib
            rw [hf'val] at hi
            simp [pairVec, hba] at hi
            rw [hb] at hi
            exact absurd hi (by decide)
          · rw [hf'val] at hi
            simpa [pairVec, hia, hib] using hi
      · intro hsub
        have := hsub (show a ∈ (Finset.univ.filter fun i => f.1 i = 1) by simp [ha])
        simp [Finset.mem_filter, hfa] at this
    have key := ih _ hlt f' rfl
    have hfeq : f = f' + pairE a b := by
      rw [hf', add_assoc, pairE_add_self, add_zero]
    rw [hfeq, QuotientAddGroup.mk_add]
    exact U.add_mem key (hpairs a b hba.symm)
  · push Not at h0
    have : f = 0 := by
      apply Subtype.ext
      funext i
      rcases zmod_two_cases (f.1 i) with h | h
      · exact h
      · exact absurd h (h0 i)
    rw [this]
    simp

theorem heart_irreducible (hd : 4 ≤ d) (U : AddSubgroup (Heart d))
    (hU : ∀ σ ∈ alternatingGroup (Fin d), ∀ u ∈ U, heartAct σ u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨u, huU⟩, hu0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hbot
  obtain ⟨u0, rfl⟩ := QuotientAddGroup.mk_surjective u
  have hnc : (u0 : PM d) ∉ constSub d := by
    intro hc
    apply hu0
    apply Subtype.ext
    exact (QuotientAddGroup.eq_zero_iff _).2 hc
  obtain ⟨a, b, c, hba, ha, hb, hc⟩ := exists_abc hnc
  have hac : a ≠ c := fun h => by
    rw [← h, ha] at hc; exact absurd hc (by decide)
  have hbc : b ≠ c := fun h => by
    rw [← h, hb] at hc; exact absurd hc (by decide)
  obtain ⟨σ, hσ, hσu⟩ := cycle_step hba hac hbc ha hb hc
  have h1 : (QuotientAddGroup.mk (pairE b c) : Heart d) ∈ U := by
    rw [← hσu, QuotientAddGroup.mk_add]
    exact U.add_mem (hU σ hσ _ huU) huU
  have hall : ∀ x y : Fin d, x ≠ y → (QuotientAddGroup.mk (pairE x y) : Heart d) ∈ U := by
    intro x y hxy
    obtain ⟨τ, hτ, hτb, hτc⟩ := exists_even_pair hd hbc hxy
    have := hU τ hτ _ h1
    rwa [heartAct_mk, actE_pairE, hτb, hτc] at this
  rw [eq_top_iff]
  intro w _
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective w
  exact mk_mem_of_pairs U hall f

theorem heart_nontrivial (hd : 3 ≤ d) : Nontrivial (Heart d) := by
  refine ⟨⟨QuotientAddGroup.mk (pairE ⟨0, by omega⟩ ⟨1, by omega⟩), 0, ?_⟩⟩
  intro h
  have hmem := (QuotientAddGroup.eq_zero_iff _).1 h
  have hc : (pairE (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩).1 ∈ constSub d := hmem
  have h01 := hc ⟨0, by omega⟩ ⟨2, by omega⟩
  simp [pairE, pairVec, Fin.ext_iff] at h01

end Heart

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
