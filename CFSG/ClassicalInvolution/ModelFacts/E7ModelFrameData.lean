module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSign
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelWeyl
public import Certificates.Certificate113

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts

local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

@[expose] def simpleV (n : ℕ) : V7 := Pi.single (e7Idx n) 1

@[expose] def JofL (L : List ℕ) : Set (Fin (Tag.rank .E7)) := {j | j.val ∉ L}

theorem mem_parabolicRoots_JofL {L : List ℕ} {σ : V7} (hσ : IsRoot .E7 σ)
    (h : ∀ i : Fin (Tag.rank .E7), i.val ∈ L → σ i = 0) :
    σ ∈ parabolicRoots .E7 (JofL L) :=
  ⟨hσ, fun i hi => h i (by simpa [JofL] using hi)⟩

@[expose] def gA : V7 := ![1, 1, 2, 2, 1, 0, 0]

@[expose] def gB : V7 := simpleV 5

@[expose] def muV : V7 := simpleV 1

@[expose] def lamB : V7 := ![7, 9, 13, 18, 14, 10, 5]

@[expose] def lamC : V7 := ![11, 15, 21, 30, 24, 17, 9]

theorem gA_mem : gA ∈ rootFinset .E7 := by decide +kernel
theorem gB_mem : gB ∈ rootFinset .E7 := by decide +kernel
theorem muV_mem : muV ∈ rootFinset .E7 := by decide +kernel

theorem isRoot_gA : IsRoot .E7 gA := mem_rootFinset.1 gA_mem
theorem isRoot_gB : IsRoot .E7 gB := mem_rootFinset.1 gB_mem
theorem isRoot_muV : IsRoot .E7 muV := mem_rootFinset.1 muV_mem

section Levi

theorem lamB_J : ∀ j ∈ JofL [0, 2, 5], iform lamB (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 5] → iform lamB (Pi.single j 1) = 0 := by
    decide +kernel
  exact this

theorem lamB_B : ∀ σ ∈ rootFinset .E7, |iform lamB σ| ≤ 7 := by decide +kernel

theorem lamB_ker : ∀ σ ∈ rootFinset .E7, iform lamB σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamB σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem lamC_J : ∀ j ∈ JofL [0, 2, 4, 5, 6], iform lamC (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] → iform lamC (Pi.single j 1) = 0 := by
    decide +kernel
  exact this

theorem lamC_B : ∀ σ ∈ rootFinset .E7, |iform lamC σ| ≤ 11 := by decide +kernel

theorem lamC_ker : ∀ σ ∈ rootFinset .E7, iform lamC σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamC σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem cut_B : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform gA σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform gA σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem cut_C : ∀ σ ∈ rootFinset .E7, iform lamB σ = 0 → Even (iform gB σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 4, 5, 6]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamB σ = 0 → Even (iform gB σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 4, 5, 6] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem JofL_le_Jsign {L : List ℕ} (h0 : 0 ∈ L) (h2 : 2 ∈ L) : JofL L ⊆ Jsign := by
  intro j hj
  change j.val ∉ L at hj
  refine ⟨fun h => hj ?_, fun h => hj ?_⟩
  · rw [h]; exact h0
  · rw [h]; exact h2

theorem gA_even_JB : ∀ j ∈ JofL [0, 2, 5], Even (iform gA (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 5] → Even (iform gA (Pi.single j 1)) := by
    decide +kernel
  exact this

theorem gA_even_JC : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform gA (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform gA (Pi.single j 1)) := by decide +kernel
  exact this

theorem gB_even_JC : ∀ j ∈ JofL [0, 2, 4, 5, 6], Even (iform gB (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 4, 5, 6] →
      Even (iform gB (Pi.single j 1)) := by decide +kernel
  exact this

end Levi

section Pin

@[expose] def pinWordsA : List (List ℕ) :=
  [[], [5], [4, 5], [6, 5], [3, 4, 5], [6, 4, 5], [1, 3, 4, 5], [5, 6, 4, 5], [6, 3, 4, 5],
    [5, 6, 3, 4, 5], [6, 1, 3, 4, 5], [4, 5, 6, 3, 4, 5], [5, 6, 1, 3, 4, 5],
    [4, 5, 6, 1, 3, 4, 5], [3, 4, 5, 6, 1, 3, 4, 5]]

theorem pin_A : ∀ γ ∈ rootFinset .E7, (iform thetaLit γ = 1 ∨ iform thetaLit γ = -1) →
    iform e0V γ = 0 → ∃ ω ∈ pinWordsA, wordAct ω γ = gA ∨ wordAct ω γ = -gA := by
  decide +kernel

theorem pinWordsA_fix : ∀ ω ∈ pinWordsA, wordAct ω thetaLit = thetaLit ∧
    wordAct ω e0V = e0V := by decide +kernel

@[expose] def pinWordsB : List (List ℕ) :=
  [[], [4], [6], [3, 4], [6, 4], [1, 3, 4], [6, 3, 4], [6, 1, 3, 4]]

theorem pin_B : ∀ γ ∈ rootFinset .E7, (iform gA γ = 1 ∨ iform gA γ = -1) →
    iform thetaLit γ = 0 → iform e0V γ = 0 →
    ∃ ω ∈ pinWordsB, wordAct ω γ = gB ∨ wordAct ω γ = -gB := by decide +kernel

theorem pinWordsB_fix : ∀ ω ∈ pinWordsB, wordAct ω thetaLit = thetaLit ∧
    wordAct ω e0V = e0V ∧ wordAct ω gA = gA := by decide +kernel

@[expose] def pinWordsC : List (List ℕ) := [[], [1], [3], [1, 3], [3, 1], [1, 3, 1]]

theorem pin_C : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    iform gA γ = 0 → iform gB γ = 0 →
    ∃ ω ∈ pinWordsC, wordAct ω γ = muV ∨ wordAct ω γ = -muV := by decide +kernel

theorem pinWordsC_fix : ∀ ω ∈ pinWordsC, wordAct ω thetaLit = thetaLit ∧
    wordAct ω e0V = e0V ∧ wordAct ω gA = gA ∧ wordAct ω gB = gB := by
  decide +kernel

end Pin

section Final

@[expose] def finalWord : List ℕ :=
  [3, 6, 4, 3, 5, 6, 4, 5, 3, 4, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

theorem finalWord_RM : wordAct finalWord (simpleV 1) = thetaLit := by
  refine wordAct_eq_of_chainB _
    [
      ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 1],
      ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1],
      ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 1],
      ![0, 1, 1, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 1], ![0, 1, 1, 2, 2, 2, 1],
      ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 2, 1],
      ![1, 1, 2, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 1],
      ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1],
      ![1, 2, 3, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]
    ] _ _ ?_
  decide +kernel

theorem finalWord_C0 : wordAct finalWord (simpleV 0) = -(simpleV 6) := by
  refine wordAct_eq_of_chainB _
    [
      ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
      ![1, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 1],
      ![0, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, -1],
      ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1],
      ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1],
      ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, -1],
      ![0, 0, 0, 0, 0, 0, -1]
    ] _ _ ?_
  decide +kernel

theorem finalWord_C1 : wordAct finalWord (thetaLit) = simpleV 5 := by
  refine wordAct_eq_of_chainB _
    [
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
      ![1, 2, 3, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
      ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 1, 0],
      ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1, 0],
      ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 0],
      ![0, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 0]
    ] _ _ ?_
  decide +kernel

theorem finalWord_C2 : wordAct finalWord (gA) = -(simpleV 4) := by
  refine wordAct_eq_of_chainB _
    [
      ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
      ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 1, 1],
      ![1, 1, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 2, 1],
      ![1, 1, 2, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 1], ![1, 1, 2, 3, 3, 2, 1],
      ![1, 1, 2, 3, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 1, 0],
      ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 0],
      ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
      ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
      ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0]
    ] _ _ ?_
  decide +kernel

theorem finalWord_C3 : wordAct finalWord (gB) = -(simpleV 3) := by
  refine wordAct_eq_of_chainB _
    [
      ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 0],
      ![0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, -1, -1, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0],
      ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0],
      ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0], ![0, 0, -1, -1, -1, 0, 0],
      ![0, 0, 0, -1, -1, 0, 0], ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0, 0],
      ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, -1, -1, 0, 0],
      ![0, 0, 0, -1, 0, 0, 0]
    ] _ _ ?_
  decide +kernel

end Final

end CFSG.ClassicalInvolution.ModelFacts.E7Model
