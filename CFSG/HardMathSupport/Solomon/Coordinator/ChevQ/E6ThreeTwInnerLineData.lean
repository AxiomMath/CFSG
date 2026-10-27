module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.SeitzPlane
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def twLineExp (v : Fin Tag.E6.rank → ℤ) : ℤ := 2 * v 0 + v 1 + v 4

theorem rootChar_twLineChar {Ω : Type} [Field Ω] (ω : Ωˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (twLineChar ω) v = ω ^ twLineExp v := by
  rw [twLineExp, zpow_add, zpow_add, zpow_mul, zpow_two]
  change ∏ i : Fin 6, twLineChar ω i ^ v i = _
  rw [Fin.prod_univ_six]
  simp [twLineChar, sq]
  rfl

section Frame

theorem twLineWeyl_smul (v : Fin Tag.E6.rank → ℤ) :
    twLineWeyl • v = e6WordAct twLineWord v :=
  prod_simple_smul_eq_e6WordAct _ _

theorem twLineWeyl_image (i : Fin 3) :
    (twLineWeyl • ·) '' twE6FrameS i = twE6FrameS (i + 1) := by
  have h1 : ∀ j : Fin 3, ∀ α ∈ twE6FrameL j, e6WordAct twLineWord α ∈ twE6FrameL (j + 1) := by
    decide +kernel
  have h2 : ∀ j : Fin 3, ∀ β ∈ twE6FrameL (j + 1), ∃ α ∈ twE6FrameL j,
      e6WordAct twLineWord α = β := by
    decide +kernel
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    change twLineWeyl • α ∈ twE6FrameL (i + 1)
    rw [twLineWeyl_smul]
    exact h1 i α hα
  · intro hβ
    obtain ⟨α, hα, hαβ⟩ := h2 i β hβ
    exact ⟨α, hα, by change twLineWeyl • α = β; rw [twLineWeyl_smul, hαβ]⟩

theorem twE6FrameS_neg {i : Fin 3} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twE6FrameS i) :
    -α ∈ twE6FrameS i := by
  have h : ∀ j : Fin 3, ∀ β ∈ twE6FrameL j, -β ∈ twE6FrameL j := by decide +kernel
  exact h i α hα

theorem twE6FrameS_neg_stable {i : Fin 3} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twE6FrameS i) :
    -(e6T3W • α) ∈ twE6FrameS i :=
  twE6FrameS_neg (twE6FrameS_stable i hα)

theorem twE6FrameWeyl_zero_image (i : Fin 3) :
    (twE6FrameWeyl 0 • ·) '' twE6FrameS i = (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) := by
  have hmul : ∀ β, twE6FrameWeyl 0 • β = wordMat Tag.E6 (twE6FrameWord 0) *ᵥ β := fun β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have h1 : ∀ j : Fin 3, ∀ α ∈ twE6FrameL j,
      wordMat Tag.E6 (twE6FrameWord 0) *ᵥ α ∈ e6LineRoots j := by
    decide +kernel
  have h2 : ∀ j : Fin 3, ∀ β ∈ e6LineRoots j, ∃ α ∈ twE6FrameL j,
      wordMat Tag.E6 (twE6FrameWord 0) *ᵥ α = β := by
    decide +kernel
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    change twE6FrameWeyl 0 • α ∈ e6LineRoots i
    rw [hmul]
    exact h1 i α hα
  · intro hβ
    obtain ⟨α, hα, hαβ⟩ := h2 i β hβ
    exact ⟨α, hα, by change twE6FrameWeyl 0 • α = β; rw [hmul, hαβ]⟩

theorem single_mem_twE6FrameS_zero :
    (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 ∧
      (-Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 ∧
      (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 ∧
      (-Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ twE6FrameS 0 := by
  change _ ∈ twE6FrameL 0 ∧ _ ∈ twE6FrameL 0 ∧ _ ∈ twE6FrameL 0 ∧ _ ∈ twE6FrameL 0
  decide +kernel

theorem twLineExp_twLineWeyl : ∀ α ∈ rootFinset .E6,
    (3 : ℤ) ∣ twLineExp (e6WordAct twLineWord α) - twLineExp α := by
  decide +kernel

theorem twLineExp_e6T3 : ∀ α ∈ rootFinset .E6,
    (3 : ℤ) ∣ twLineExp (toMat Tag.E6.rank e6T3MList *ᵥ α) - twLineExp α := by
  decide +kernel

theorem twLineExp_frame : ∀ α ∈ rootFinset .E6,
    (3 : ℤ) ∣ (wordMat Tag.E6 (twE6FrameWord 0) *ᵥ α) e6KacNode - twLineExp α := by
  decide +kernel

@[expose] def twLineDL : Fin 2 → List (Fin Tag.E6.rank → ℤ)
  | 0 => [![1, 1, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1],
      ![-1, -1, -1, -1, -1, -1], ![-1, 0, 0, 0, 0, 0], ![0, -1, -1, -1, -1, -1]]
  | 1 => [![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
      ![0, -1, 0, -1, -1, 0], ![0, -1, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0]]

@[expose] def twLineDS (j : Fin 2) : Set (Fin Tag.E6.rank → ℤ) := {α | α ∈ twLineDL j}

@[expose] def twLineXWord : Fin 2 → List (Fin Tag.E6.rank)
  | 0 => [3, 4, 5, 1]
  | 1 => [3, 4, 2, 3, 0, 2, 1]

@[expose] def twLineXW (j : Fin 2) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (twLineXWord j)

@[expose] def twLineRWord : Fin 2 → List (Fin Tag.E6.rank)
  | 0 => [0, 2]
  | 1 => [2, 0]

@[expose] def twLineCWord (j : Fin 2) : List (Fin Tag.E6.rank) :=
  (twLineXWord j).reverse ++ twLineRWord j ++ twLineXWord j

@[expose] def twLineCW (j : Fin 2) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (twLineCWord j)

theorem twLineDS_root {j : Fin 2} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twLineDS j) :
    IsRoot Tag.E6 α := by
  have h : ∀ k : Fin 2, ∀ β ∈ twLineDL k, β ∈ rootFinset .E6 := by decide +kernel
  exact mem_rootFinset.1 (h j α hα)

theorem twLineDS_stable {j : Fin 2} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twLineDS j) :
    e6T3W • α ∈ twLineDS j := by
  rw [← weylMatrix_mulVec, weylMatrix_e6T3W]
  have h : ∀ k : Fin 2, ∀ β ∈ twLineDL k,
      (toMat Tag.E6.rank e6T3MList *ᵥ β) ∈ twLineDL k := by decide +kernel
  exact h j α hα

theorem twLineDS_neg {j : Fin 2} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twLineDS j) :
    -α ∈ twLineDS j := by
  have h : ∀ k : Fin 2, ∀ β ∈ twLineDL k, -β ∈ twLineDL k := by decide +kernel
  exact h j α hα

theorem twLineDS_neg_stable {j : Fin 2} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ twLineDS j) :
    -(e6T3W • α) ∈ twLineDS j :=
  twLineDS_neg (twLineDS_stable hα)

theorem twLineDS_conj (j : Fin 2) :
    (twLineXW j • ·) '' twLineDS j = parabolicRoots Tag.E6 support13 := by
  rw [twE6Phi13_eq]
  have hmul : ∀ β, twLineXW j • β = wordMat Tag.E6 (twLineXWord j) *ᵥ β := fun β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have h1 : ∀ k : Fin 2, ∀ β ∈ twLineDL k,
      (wordMat Tag.E6 (twLineXWord k) *ᵥ β) ∈ twE6Phi13L := by decide +kernel
  have h2 : ∀ k : Fin 2, ∀ α ∈ twE6Phi13L, ∃ β ∈ twLineDL k,
      wordMat Tag.E6 (twLineXWord k) *ᵥ β = α := by decide +kernel
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    change twLineXW j • β ∈ twE6Phi13L
    rw [hmul]
    exact h1 j β hβ
  · intro hα
    obtain ⟨β, hβ, hβα⟩ := h2 j α hα
    exact ⟨β, hβ, by change twLineXW j • β = α; rw [hmul, hβα]⟩

theorem twLineCW_eq (j : Fin 2) :
    twLineCW j = (twLineXW j)⁻¹ * (coxeterSystem Tag.E6).wordProd (twLineRWord j) *
      twLineXW j := by
  rw [twLineCW, twLineCWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_reverse, twLineXW]

theorem twLineCW_comm (j : Fin 2) : twLineCW j * e6T3W = e6T3W * twLineCW j := by
  have hmul : ∀ (k : Fin 2) (β : Fin Tag.E6.rank → ℤ),
      twLineCW k • β = wordMat Tag.E6 (twLineCWord k) *ᵥ β := fun k β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have hu : ∀ β : Fin Tag.E6.rank → ℤ, e6T3W • β = toMat Tag.E6.rank e6T3MList *ᵥ β := fun β => by
    rw [← weylMatrix_mulVec, weylMatrix_e6T3W]
  have h : ∀ (k : Fin 2) (i : Fin Tag.E6.rank),
      wordMat Tag.E6 (twLineCWord k) *ᵥ (toMat Tag.E6.rank e6T3MList *ᵥ Pi.single i 1) =
        toMat Tag.E6.rank e6T3MList *ᵥ (wordMat Tag.E6 (twLineCWord k) *ᵥ Pi.single i 1) := by
    decide +kernel
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, hu, hmul, hmul, hu]
  exact h j i

theorem twLineCW_mul : twLineCW 0 * twLineCW 1 = twLineWeyl := by
  have hmul : ∀ (k : Fin 2) (β : Fin Tag.E6.rank → ℤ),
      twLineCW k • β = wordMat Tag.E6 (twLineCWord k) *ᵥ β := fun k β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have h : ∀ i : Fin Tag.E6.rank,
      wordMat Tag.E6 (twLineCWord 0) *ᵥ (wordMat Tag.E6 (twLineCWord 1) *ᵥ Pi.single i 1) =
        e6WordAct twLineWord (Pi.single i 1) := by
    decide +kernel
  refine ext_single fun i => ?_
  rw [mul_smul, hmul, hmul, twLineWeyl_smul]
  exact h i

theorem single_mem_parabolicRoots_support13 {i : Fin Tag.E6.rank} (hi : i = 0 ∨ i = 2) :
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 ∧
      (-Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 := by
  rw [twE6Phi13_eq]
  change _ ∈ twE6Phi13L ∧ _ ∈ twE6Phi13L
  rcases hi with rfl | rfl <;> decide +kernel

@[expose] def twLinePhi56L : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, -1, -1]]

theorem twLinePhi56_eq : parabolicRoots Tag.E6 support56 = {α | α ∈ twLinePhi56L} := by
  ext α
  constructor
  · rintro ⟨hα, hz⟩
    have h : ∀ β ∈ rootFinset .E6, β 0 = 0 → β 1 = 0 → β 2 = 0 → β 3 = 0 →
        β ∈ twLinePhi56L := by decide +kernel
    have hn : ∀ k : Fin Tag.E6.rank, k.val ≠ 4 → k.val ≠ 5 → α k = 0 := fun k h4 h5 =>
      hz k (by
        rw [mem_support56]
        rintro (h | h)
        · exact h4 (by rw [h]; rfl)
        · exact h5 (by rw [h]; rfl))
    exact h α (mem_rootFinset.2 hα) (hn 0 (by decide) (by decide)) (hn 1 (by decide) (by decide))
      (hn 2 (by decide) (by decide)) (hn 3 (by decide) (by decide))
  · intro hα
    have h : ∀ β ∈ twLinePhi56L, β ∈ rootFinset .E6 ∧ β 0 = 0 ∧ β 1 = 0 ∧ β 2 = 0 ∧ β 3 = 0 := by
      decide +kernel
    obtain ⟨h1, h2, h3, h4, h5⟩ := h α hα
    refine ⟨mem_rootFinset.1 h1, fun k hk => ?_⟩
    fin_cases k
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact absurd (by rw [mem_support56]; exact Or.inl rfl) hk
    · exact absurd (by rw [mem_support56]; exact Or.inr rfl) hk

@[expose] def twLineYWord : List (Fin Tag.E6.rank) := [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 1, 0]

@[expose] def twLineYW : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd twLineYWord

theorem twLineYW_image_one :
    (twLineYW • ·) '' twE6FrameS 1 = parabolicRoots Tag.E6 support13 := by
  rw [twE6Phi13_eq]
  have hmul : ∀ β, twLineYW • β = wordMat Tag.E6 twLineYWord *ᵥ β := fun β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have h1 : ∀ β ∈ twE6FrameL 1, (wordMat Tag.E6 twLineYWord *ᵥ β) ∈ twE6Phi13L := by
    decide +kernel
  have h2 : ∀ α ∈ twE6Phi13L, ∃ β ∈ twE6FrameL 1, wordMat Tag.E6 twLineYWord *ᵥ β = α := by
    decide +kernel
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    change twLineYW • β ∈ twE6Phi13L
    rw [hmul]
    exact h1 β hβ
  · intro hα
    obtain ⟨β, hβ, hβα⟩ := h2 α hα
    exact ⟨β, hβ, by change twLineYW • β = α; rw [hmul, hβα]⟩

theorem twLineYW_image_two :
    (twLineYW • ·) '' twE6FrameS 2 = parabolicRoots Tag.E6 support56 := by
  rw [twLinePhi56_eq]
  have hmul : ∀ β, twLineYW • β = wordMat Tag.E6 twLineYWord *ᵥ β := fun β =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec _ _ β
  have h1 : ∀ β ∈ twE6FrameL 2, (wordMat Tag.E6 twLineYWord *ᵥ β) ∈ twLinePhi56L := by
    decide +kernel
  have h2 : ∀ α ∈ twLinePhi56L, ∃ β ∈ twE6FrameL 2, wordMat Tag.E6 twLineYWord *ᵥ β = α := by
    decide +kernel
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    change twLineYW • β ∈ twLinePhi56L
    rw [hmul]
    exact h1 β hβ
  · intro hα
    obtain ⟨β, hβ, hβα⟩ := h2 α hα
    exact ⟨β, hβ, by change twLineYW • β = α; rw [hmul, hβα]⟩

@[expose] def twLineBlk : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

@[expose] def twLineNode : Fin 6 → Fin Tag.E6.rank := ![0, 2, 0, 2, 0, 2]

@[expose] def twLineCocharA : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1, 0, 1, 0, 1, -1; 0, -1, -1, 0, 1, 0; 2, -1, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0;
    0, -1, 1, -1, -1, 1; 0, 0, -1, 2, 0, 0]

@[expose] def twLineCocharB : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 6, 3, 0, 0; 0, 0, 3, 6, 0, 0; 6, 0, 6, 6, 6, 3; 3, 0, 3, 3, 3, 6;
    6, 9, 9, 12, 6, 3; 3, 9, 9, 15, 12, 6]

theorem twLineCocharA_apply : ∀ k m : Fin 6, twLineCocharA m k =
    ∑ l : Fin Tag.E6.rank, Tag.E6.cartan (twLineNode k) l *
      (wordMat Tag.E6 (twE6FrameWord (twLineBlk k)) *ᵥ Pi.single m 1) l := by
  decide +kernel

theorem twLineCochar_mul : twLineCocharA * twLineCocharB = (9 : ℤ) • 1 := by
  decide +kernel

theorem twLineCocharA_det_ne_zero : twLineCocharA.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det twLineCochar_mul
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, h0, zero_mul] at h
  norm_num at h

end Frame

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
