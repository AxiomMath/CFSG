module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPerm

public section

namespace CFSG.OddStandard.SmallF3.Omega

private abbrev l16f4PairCond (a b sa sb : Fin 8) : Prop :=
  ((Pi.single sa (1 : ZMod 2) + Pi.single sb 1 : Fin 8 → ZMod 2) +
      (Pi.single a 1 + Pi.single b 1) = 0) ∨
    ((Pi.single sa (1 : ZMod 2) + Pi.single sb 1 : Fin 8 → ZMod 2) +
      (Pi.single a 1 + Pi.single b 1) = 1)

private theorem l16f4_first : ∀ s0 s1 s2 s3 : Fin 8,
    l16f4PairCond 0 1 s0 s1 → l16f4PairCond 0 2 s0 s2 → l16f4PairCond 0 3 s0 s3 →
    l16f4PairCond 1 2 s1 s2 → l16f4PairCond 1 3 s1 s3 → l16f4PairCond 2 3 s2 s3 →
      s0 = 0 ∧ s1 = 1 ∧ s2 = 2 ∧ s3 = 3 := by
  decide +kernel

private theorem l16f4_second : ∀ s4 s5 s6 s7 : Fin 8,
    l16f4PairCond 4 5 s4 s5 → l16f4PairCond 4 6 s4 s6 → l16f4PairCond 4 7 s4 s7 →
    l16f4PairCond 5 6 s5 s6 → l16f4PairCond 5 7 s5 s7 → l16f4PairCond 6 7 s6 s7 →
      s4 = 4 ∧ s5 = 5 ∧ s6 = 6 ∧ s7 = 7 := by
  decide +kernel

private theorem l16f4_isFirst : ∀ a b : Fin 8, (a : ℕ) < 4 → (b : ℕ) < 4 →
    IsFirstBlockVec (Pi.single a (1 : ZMod 2) + Pi.single b 1 : Fin 8 → ZMod 2) := by
  unfold IsFirstBlockVec IsEvenVec
  decide +kernel

private theorem l16f4_isSecond : ∀ a b : Fin 8, 4 ≤ (a : ℕ) → 4 ≤ (b : ℕ) →
    IsSecondBlockVec (Pi.single a (1 : ZMod 2) + Pi.single b 1 : Fin 8 → ZMod 2) := by
  unfold IsSecondBlockVec IsEvenVec
  decide +kernel

private theorem l16f4_permVec_single (σ : Equiv.Perm (Fin 8)) (a : Fin 8) :
    permVec σ (Pi.single a (1 : ZMod 2)) = Pi.single (σ a) 1 := by
  funext i
  simp only [permVec, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem heartPerm_eq_one_of_blocks (σ : Equiv.Perm (Fin 8))
    (h1 : ∀ w : Fin 8 → ZMod 2, IsFirstBlockVec w →
      permVec σ w + w = 0 ∨ permVec σ w + w = 1)
    (h2 : ∀ w : Fin 8 → ZMod 2, IsSecondBlockVec w →
      permVec σ w + w = 0 ∨ permVec σ w + w = 1) : σ = 1 := by
  have key1 : ∀ a b : Fin 8, (a : ℕ) < 4 → (b : ℕ) < 4 → l16f4PairCond a b (σ a) (σ b) := by
    intro a b ha hb
    have h := h1 _ (l16f4_isFirst a b ha hb)
    rw [sec5b_permVec_add, l16f4_permVec_single, l16f4_permVec_single] at h
    exact h
  have key2 : ∀ a b : Fin 8, 4 ≤ (a : ℕ) → 4 ≤ (b : ℕ) → l16f4PairCond a b (σ a) (σ b) := by
    intro a b ha hb
    have h := h2 _ (l16f4_isSecond a b ha hb)
    rw [sec5b_permVec_add, l16f4_permVec_single, l16f4_permVec_single] at h
    exact h
  obtain ⟨e0, e1, e2, e3⟩ := l16f4_first (σ 0) (σ 1) (σ 2) (σ 3)
    (key1 0 1 (by decide) (by decide)) (key1 0 2 (by decide) (by decide))
    (key1 0 3 (by decide) (by decide)) (key1 1 2 (by decide) (by decide))
    (key1 1 3 (by decide) (by decide)) (key1 2 3 (by decide) (by decide))
  obtain ⟨e4, e5, e6, e7⟩ := l16f4_second (σ 4) (σ 5) (σ 6) (σ 7)
    (key2 4 5 (by decide) (by decide)) (key2 4 6 (by decide) (by decide))
    (key2 4 7 (by decide) (by decide)) (key2 5 6 (by decide) (by decide))
    (key2 5 7 (by decide) (by decide)) (key2 6 7 (by decide) (by decide))
  ext i
  fin_cases i <;> simp [e0, e1, e2, e3, e4, e5, e6, e7]

end CFSG.OddStandard.SmallF3.Omega
