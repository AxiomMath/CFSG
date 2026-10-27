module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44GolayCol

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSporadicStandard.Wong77.Module

set_option compiler.extract_closed false

@[expose] def initSeg (k : ℕ) : Finset (Fin 23) := Finset.univ.filter fun x => x.val < k

@[expose] def golayBasePt (k : ℕ) : Fin 23 := ⟨k % 23, Nat.mod_lt _ (by norm_num)⟩

@[expose] def golayCol1 (k : ℕ) : List ℕ := stepCol (initCol (initSeg k))

@[expose] def golayCol2 (k : ℕ) : List ℕ := stepCol (golayCol1 k)

@[expose] def colClass (l : List ℕ) (b : Fin 23) : Finset (Fin 23) :=
  Finset.univ.filter fun q => colAt l q = colAt l b

@[expose] def colInjCheck (l : List ℕ) : Bool :=
  (List.finRange 23).all fun p => (List.finRange 23).all fun q =>
    decide (colAt l p = colAt l q → p = q)

@[expose] def golayAutCheck : Bool :=
  (colClass (golayCol1 1) (golayBasePt 1)).card == 22 &&
    (colClass (golayCol1 2) (golayBasePt 2)).card == 21 &&
    (colClass (golayCol1 3) (golayBasePt 3)).card == 20 &&
    (colClass (golayCol1 4) (golayBasePt 4)).card == 3 &&
    (colClass (golayCol1 5) (golayBasePt 5)).card == 16 && colInjCheck (golayCol2 6)

theorem golayAutCheck_sound (h : golayAutCheck = true) :
    (colClass (golayCol1 1) (golayBasePt 1)).card = 22 ∧
      (colClass (golayCol1 2) (golayBasePt 2)).card = 21 ∧
      (colClass (golayCol1 3) (golayBasePt 3)).card = 20 ∧
      (colClass (golayCol1 4) (golayBasePt 4)).card = 3 ∧
      (colClass (golayCol1 5) (golayBasePt 5)).card = 16 ∧
      ∀ p q, colAt (golayCol2 6) p = colAt (golayCol2 6) q → p = q := by
  simp only [golayAutCheck, colInjCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_finRange, forall_const, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem colAt_golayCol1_perm {k : ℕ} {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    (hk : ∀ x : Fin 23, x.val < k → g x = x) (p : Fin 23) :
    colAt (golayCol1 k) (g p) = colAt (golayCol1 k) p :=
  colAt_stepCol_perm hg (colAt_initCol_perm fun d hd => hk d (by simpa [initSeg] using hd)) p

theorem mem_colClass_golayCol1 {k : ℕ} {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    (hk : ∀ x : Fin 23, x.val < k → g x = x) (b : Fin 23) :
    g b ∈ colClass (golayCol1 k) b :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, colAt_golayCol1_perm hg hk b⟩

theorem eq_one_of_fix_six (hinj : ∀ p q, colAt (golayCol2 6) p = colAt (golayCol2 6) q → p = q)
    {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    (hk : ∀ x : Fin 23, x.val < 6 → g x = x) : g = 1 := by
  refine Equiv.ext fun p => ?_
  exact hinj _ _ (colAt_stepCol_perm hg (colAt_golayCol1_perm hg hk) p)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
