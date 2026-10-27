module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice
open scoped Matrix

section Main

set_option linter.unusedSectionVars false


@[expose] def twE6FrameL : Fin 3 → List (Fin Tag.E6.rank → ℤ)
  | 0 => [![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0],
      ![0, 0, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, -1, -1, 0, 0]]
  | 1 => [![0, 0, 0, 0, 0, 1], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, -1], ![-1, 0, -1, -1, -1, 0], ![-1, 0, -1, -1, -1, -1]]
  | 2 => [![1, 2, 2, 3, 2, 1], ![1, 1, 1, 1, 0, 0], ![0, 1, 1, 2, 2, 1],
      ![-1, -2, -2, -3, -2, -1], ![-1, -1, -1, -1, 0, 0], ![0, -1, -1, -2, -2, -1]]

@[expose] def twE6FrameS (i : Fin 3) : Set (Fin Tag.E6.rank → ℤ) := {α | α ∈ twE6FrameL i}

@[expose] def twE6FrameWord : Fin 3 → List (Fin Tag.E6.rank)
  | 0 => [3, 2, 0]
  | 1 => [3, 4, 5, 2, 3, 4]
  | 2 => [3, 4, 5, 1, 3, 4, 2, 3, 1]

@[expose] def twE6FrameWeyl (i : Fin 3) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (twE6FrameWord i)

@[expose] def twE6Phi13L : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![-1, 0, -1, 0, 0, 0]]

theorem twE6FrameL_mem_rootFinset : ∀ i : Fin 3, ∀ α ∈ twE6FrameL i, α ∈ rootFinset .E6 := by
  decide +kernel

theorem twE6FrameS_root (i : Fin 3) {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twE6FrameS i) :
    IsRoot Tag.E6 α :=
  mem_rootFinset.1 (twE6FrameL_mem_rootFinset i α hα)

theorem twE6FrameS_stable (i : Fin 3) {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twE6FrameS i) :
    e6T3W • α ∈ twE6FrameS i := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W]
  have h : ∀ j : Fin 3, ∀ β ∈ twE6FrameL j,
      (toMat Tag.E6.rank e6T3MList *ᵥ β) ∈ twE6FrameL j := by decide +kernel
  exact h i α hα

theorem twE6FrameS_orth {i j : Fin 3} (hij : i ≠ j) :
    ∀ α ∈ twE6FrameS i, ∀ β ∈ twE6FrameS j,
      α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0 := by
  have h : ∀ i j : Fin 3, i ≠ j → ∀ α ∈ twE6FrameL i, ∀ β ∈ twE6FrameL j,
      α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0 := by decide +kernel
  exact h i j hij

theorem twE6Phi13_eq : parabolicRoots Tag.E6 support13 = {α | α ∈ twE6Phi13L} := by
  ext α
  constructor
  · rintro ⟨hα, hz⟩
    have h : ∀ β ∈ rootFinset .E6, β 1 = 0 → β 3 = 0 → β 4 = 0 → β 5 = 0 →
        β ∈ twE6Phi13L := by decide +kernel
    have hn : ∀ k : Fin Tag.E6.rank, k.val ≠ 0 → k.val ≠ 2 → α k = 0 := fun k h0 h2 =>
      hz k (by
        rw [mem_support13]
        rintro (h | h)
        · exact h0 (by rw [h]; rfl)
        · exact h2 (by rw [h]; rfl))
    exact h α (mem_rootFinset.2 hα) (hn 1 (by decide) (by decide)) (hn 3 (by decide) (by decide))
      (hn 4 (by decide) (by decide)) (hn 5 (by decide) (by decide))
  · intro hα
    have h : ∀ β ∈ twE6Phi13L, β ∈ rootFinset .E6 ∧ β 1 = 0 ∧ β 3 = 0 ∧ β 4 = 0 ∧ β 5 = 0 := by
      decide +kernel
    obtain ⟨h1, h2, h3, h4, h5⟩ := h α hα
    refine ⟨mem_rootFinset.1 h1, fun k hk => ?_⟩
    fin_cases k
    · exact absurd (by rw [mem_support13]; exact Or.inl rfl) hk
    · exact h2
    · exact absurd (by rw [mem_support13]; exact Or.inr rfl) hk
    · exact h3
    · exact h4
    · exact h5

theorem twE6FrameS_conj (i : Fin 3) :
    ((twE6FrameWeyl i) • ·) '' twE6FrameS i = parabolicRoots Tag.E6 support13 := by
  rw [twE6Phi13_eq]
  have hmul : ∀ β, twE6FrameWeyl i • β = wordMat Tag.E6 (twE6FrameWord i) *ᵥ β := fun β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    change twE6FrameWeyl i • β ∈ _
    rw [hmul]
    have h : ∀ j : Fin 3, ∀ β ∈ twE6FrameL j,
        (wordMat Tag.E6 (twE6FrameWord j) *ᵥ β) ∈ twE6Phi13L := by decide +kernel
    exact h i β hβ
  · intro hα
    have h : ∀ j : Fin 3, ∀ α ∈ twE6Phi13L, ∃ β ∈ twE6FrameL j,
        wordMat Tag.E6 (twE6FrameWord j) *ᵥ β = α := by decide +kernel
    obtain ⟨β, hβ, hβα⟩ := h i α hα
    exact ⟨β, hβ, by change twE6FrameWeyl i • β = α; rw [hmul, hβα]⟩

end Main

end CFSG.HardMathSupport.Lang.SeitzPlane
