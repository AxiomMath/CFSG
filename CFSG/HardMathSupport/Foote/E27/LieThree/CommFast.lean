module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatChecks
public import CFSG.HardMathSupport.Foote.E27.LieThree.MatTableP
public meta import CFSG.HardMathSupport.Foote.E27.LieThree.MatTableP
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Sporadic.He.Native

@[expose] def candIdx (c : AM → Bool) (T : RawTab) : List ℕ :=
  (List.range T.elts.size).filter fun b => c T.elts[b]!

@[expose] def commOKc (cand : List ℕ) (T : RawTab) : Bool :=
  (List.range T.elts.size).all fun a =>
    (a == 0) || !(tabMul T.par T.L a (tabMul T.par T.L a a) == 0) ||
    decide (81 ≤ (cand.filter fun b => tabMul T.par T.L a b == tabMul T.par T.L b a).length)

section Spec

variable {G : Type*} [Group G] {g : ℕ → G} {m : ℕ}

theorem commOKc_hyps [Finite G] (c : AM → Bool) (T : RawTab)
    (hT : TabData g T.par T.L T.elts.size m)
    (hc : commOKc (candIdx c T) T = true) {S₀ : Subgroup G}
    (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ i < T.elts.size, tabElt g T.par i = x)
    (hn : T.elts.size = 3 ^ (Nat.card G).factorization 3) :
    Nat.card S₀ = 3 ^ (Nat.card G).factorization 3 ∧
      ∀ s ∈ S₀, orderOf s = 3 → 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({s} : Set G)) := by
  refine TabData.sylow_kill hT hS₀ hn ?_
  unfold commOKc at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at hc
  intro a ha ha0 hcube
  rcases hc a ha with (h0 | h1) | h2
  · exact absurd h0 ha0
  · rw [hcube] at h1; simp at h1
  · refine h2.trans ?_
    unfold tabComm
    rw [List.countP_eq_length_filter]
    unfold candIdx
    rw [List.filter_filter]
    refine List.Sublist.length_le (List.monotone_filter_right _ ?_)
    intro b hb
    simp only [Bool.and_eq_true] at hb
    exact hb.1

end Spec

end CFSG.HardMathSupport.Foote.E27
