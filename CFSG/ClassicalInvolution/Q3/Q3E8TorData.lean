module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclStarData

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.E7Model

set_option linter.unusedSectionVars false


local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

@[expose] def chG3 : V7 := ![1, 1, 2, 2, 1, 0, 0]

@[expose] def chG4 : V7 := simpleV 5

@[expose] def chG5a : V7 := simpleV 4

@[expose] def chG5b : V7 := simpleV 6

theorem chG3_mem : chG3 ∈ rootFinset .E7 := by decide +kernel
theorem chG4_mem : chG4 ∈ rootFinset .E7 := by decide +kernel
theorem chG5a_mem : chG5a ∈ rootFinset .E7 := by decide +kernel
theorem chG5b_mem : chG5b ∈ rootFinset .E7 := by decide +kernel

theorem isRoot_chG3 : IsRoot .E7 chG3 := mem_rootFinset.1 chG3_mem
theorem isRoot_chG4 : IsRoot .E7 chG4 := mem_rootFinset.1 chG4_mem
theorem isRoot_chG5a : IsRoot .E7 chG5a := mem_rootFinset.1 chG5a_mem
theorem isRoot_chG5b : IsRoot .E7 chG5b := mem_rootFinset.1 chG5b_mem

section Levi

@[expose] def chLam1 : V7 := ![14, 18, 26, 36, 28, 20, 10]

@[expose] def chLam2 : V7 := ![22, 30, 42, 60, 48, 34, 18]

@[expose] def chLam3a : V7 := ![30, 42, 58, 84, 66, 46, 24]

@[expose] def chLam3b : V7 := ![22, 30, 42, 60, 48, 34, 18]

theorem chLam1_J : ∀ j ∈ JofL [0, 2, 5], iform chLam1 (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 5] →
      iform chLam1 (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem chLam1_B : ∀ σ ∈ rootFinset .E7, |iform chLam1 σ| ≤ 14 := by decide +kernel

theorem chLam1_ker : ∀ σ ∈ rootFinset .E7, iform chLam1 σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam1 σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem chLam2_J : ∀ j ∈ JofL [0, 2, 4, 5, 6], iform chLam2 (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      iform chLam2 (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem chLam2_B : ∀ σ ∈ rootFinset .E7, |iform chLam2 σ| ≤ 22 := by decide +kernel

theorem chLam2_ker : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem chLam3a_J : ∀ j ∈ JofL [0, 2, 3, 4, 5, 6], iform chLam3a (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3, 4, 5, 6] →
      iform chLam3a (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem chLam3a_B : ∀ σ ∈ rootFinset .E7, |iform chLam3a σ| ≤ 30 := by decide +kernel

theorem chLam3a_ker : ∀ σ ∈ rootFinset .E7, iform chLam3a σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 3, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam3a σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 3, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem chLam3b_J : ∀ j ∈ JofL [0, 2, 4, 5, 6], iform chLam3b (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      iform chLam3b (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem chLam3b_B : ∀ σ ∈ rootFinset .E7, |iform chLam3b σ| ≤ 22 := by decide +kernel

theorem chLam3b_ker : ∀ σ ∈ rootFinset .E7, iform chLam3b σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam3b σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem ch_cut1 : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform chG3 σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform chG3 σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem ch_cut2 : ∀ σ ∈ rootFinset .E7, iform chLam1 σ = 0 → Even (iform chG4 σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam1 σ = 0 → Even (iform chG4 σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem ch_cut3a : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 → Even (iform chG5a σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 3, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 → Even (iform chG5a σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 3, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem ch_cut3b : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 → Even (iform chG5b σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 → Even (iform chG5b σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem chG3_even_J1 : ∀ j ∈ JofL [0, 2, 5], Even (iform chG3 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 5] →
      Even (iform chG3 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG3_even_J2 : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform chG3 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform chG3 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG4_even_J2 : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform chG4 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform chG4 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG3_even_J3a : ∀ j ∈ JofL [0, 2, 3, 4, 5, 6], Even (iform chG3 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3, 4, 5, 6] →
      Even (iform chG3 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG4_even_J3a : ∀ j ∈ JofL [0, 2, 3, 4, 5, 6], Even (iform chG4 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3, 4, 5, 6] →
      Even (iform chG4 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG5a_even_J3a : ∀ j ∈ JofL [0, 2, 3, 4, 5, 6], Even (iform chG5a (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3, 4, 5, 6] →
      Even (iform chG5a (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG3_even_J3b : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform chG3 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform chG3 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG4_even_J3b : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform chG4 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform chG4 (Pi.single j 1)) := by decide +kernel
  exact this

theorem chG5b_even_J3b : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform chG5b (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform chG5b (Pi.single j 1)) := by decide +kernel
  exact this

end Levi

section Pin

@[expose] def chPin3 : List (List ℕ) :=
[
  [], [5], [4, 5], [6, 5], [3, 4, 5], [6, 4, 5], [1, 3, 4, 5], [5, 6, 4, 5], [6, 3, 4, 5],
  [5, 6, 3, 4, 5], [6, 1, 3, 4, 5], [4, 5, 6, 3, 4, 5], [5, 6, 1, 3, 4, 5],
  [4, 5, 6, 1, 3, 4, 5], [3, 4, 5, 6, 1, 3, 4, 5]
]

theorem ch_pin3 : ∀ γ ∈ rootFinset .E7, (iform thetaLit γ = 1 ∨ iform thetaLit γ = -1) →
    iform e0V γ = 0 → ∃ ω ∈ chPin3, wordAct ω γ = chG3 ∨ wordAct ω γ = -chG3 := by decide +kernel

theorem chPin3_fix : ∀ ω ∈ chPin3,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) := by decide +kernel

@[expose] def chPin4 : List (List ℕ) :=
[
  [], [4], [6], [3, 4], [6, 4], [1, 3, 4], [6, 3, 4], [6, 1, 3, 4]
]

theorem ch_pin4 : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    (iform chG3 γ = 1 ∨ iform chG3 γ = -1) →
    ∃ ω ∈ chPin4, wordAct ω γ = chG4 ∨ wordAct ω γ = -chG4 := by decide +kernel

theorem chPin4_fix : ∀ ω ∈ chPin4,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
    (wordAct ω chG3 = chG3 ∨ wordAct ω chG3 = -chG3) := by decide +kernel

@[expose] def chPin5 : List (List ℕ) :=
[
  [], [3], [1, 3]
]

theorem ch_pin5 : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    iform chG3 γ = 0 → (iform chG4 γ = 1 ∨ iform chG4 γ = -1) →
    ∃ ω ∈ chPin5, (wordAct ω γ = chG5a ∨ wordAct ω γ = -chG5a) ∨
      (wordAct ω γ = chG5b ∨ wordAct ω γ = -chG5b) := by decide +kernel

theorem chPin5_fix : ∀ ω ∈ chPin5,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
    (wordAct ω chG3 = chG3 ∨ wordAct ω chG3 = -chG3) ∧
    (wordAct ω chG4 = chG4 ∨ wordAct ω chG4 = -chG4) := by decide +kernel

end Pin

section Regular

@[expose] def chRegA : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [
    (-3, -5, -5, 2, 0, 1), (0, 3, 5, -5, 2, 1)]

theorem ch_regular_a : ∀ δ ∈ rootFinset .E7, iform e0V δ = 0 → iform thetaLit δ = 0 →
    iform chG3 δ = 0 → iform chG4 δ = 0 → iform chG5a δ = 0 →
    ∃ c ∈ chRegA, ∀ σ ∈ rootFinset .E7,
      iform (c.1 • e0V + c.2.1 • thetaLit + c.2.2.1 • chG3 + c.2.2.2.1 • chG4 +
        c.2.2.2.2.1 • chG5a + c.2.2.2.2.2 • δ) σ ≠ 0 := by decide +kernel

@[expose] def chRegB : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [
    (-3, -5, -5, 2, 0, -1), (-3, -5, -5, 2, 0, 1), (-2, -5, -5, 3, 0, 1), (0, -2, -5, 5, -3, -1),
    (0, 4, 5, -5, 1, 3)]

theorem ch_regular_b : ∀ δ ∈ rootFinset .E7, iform e0V δ = 0 → iform thetaLit δ = 0 →
    iform chG3 δ = 0 → iform chG4 δ = 0 → iform chG5b δ = 0 →
    ∃ c ∈ chRegB, ∀ σ ∈ rootFinset .E7,
      iform (c.1 • e0V + c.2.1 • thetaLit + c.2.2.1 • chG3 + c.2.2.2.1 • chG4 +
        c.2.2.2.2.1 • chG5b + c.2.2.2.2.2 • δ) σ ≠ 0 := by decide +kernel

end Regular

end CFSG.ClassicalInvolution.Q3.Q3W
