module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxUnitary
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace QuasiF4

@[expose] def wF4 : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd TwClass.wordF4

theorem S₂_eq : TwClass.f4Six.S₂ = {r | r ∈ f4ShortList} := by
  ext β
  constructor
  · rintro ⟨hβ, hs⟩
    exact (f4_S₂_sub β (mem_rootFinset.2 hβ) hs)
  · intro hβ
    exact ⟨mem_rootFinset.1 (f4_short_root β hβ).1, (f4_short_root β hβ).2⟩
where
  f4_S₂_sub : ∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      β ∈ f4ShortList := by decide +kernel
  f4_short_root : ∀ β ∈ f4ShortList, β ∈ rootFinset Tag.F4 ∧
      ∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0 := by decide +kernel

theorem S₁_eq : TwClass.f4Six.S₁ = {r | r ∈ f4LongList} := by
  ext β
  show (IsRoot Tag.F4 β ∧ ∀ α ∈ TwClass.f4Six.S₂, iform (τ := Tag.F4) β α = 0) ↔ β ∈ f4LongList
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₁_sub β (mem_rootFinset.2 hβ) fun α hα => by
      rw [S₂_eq] at hs
      exact hs α hα
  · intro hβ
    refine ⟨mem_rootFinset.1 (long_root β hβ).1, fun α hα => ?_⟩
    rw [S₂_eq] at hα
    exact (long_root β hβ).2 α hα
where
  S₁_sub : ∀ β ∈ rootFinset Tag.F4, (∀ α ∈ f4ShortList, iform (τ := Tag.F4) β α = 0) →
      β ∈ f4LongList := by decide +kernel
  long_root : ∀ β ∈ f4LongList, β ∈ rootFinset Tag.F4 ∧
      ∀ α ∈ f4ShortList, iform (τ := Tag.F4) β α = 0 := by decide +kernel

theorem long_graph : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ (wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j) =
      wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong (π j) (π i) := by decide +kernel

theorem short_graph : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ f4ShortSigma i j = f4ShortSigma (π j) (π i) := by
  decide +kernel

theorem S₁_eq_chain : TwClass.f4Six.S₁ =
    {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} := by
  rw [S₁_eq]
  ext r
  show r ∈ f4LongList ↔ ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j
  simp only [f4LongV_smul]
  constructor
  · intro hr
    obtain ⟨i, j, hij, h⟩ := long_cover r hr
    exact ⟨i, j, hij, h⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact long_img i j hij

theorem S₂_eq_chain : TwClass.f4Six.S₂ = {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} := by
  rw [S₂_eq]
  ext r
  show r ∈ f4ShortList ↔ ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j
  constructor
  · intro hr
    exact short_cover r hr
  · rintro ⟨i, j, hij, rfl⟩
    exact short_img i j hij


theorem w_smul (x : Fin Tag.F4.rank → ℤ) :
    (wF4 • x : Fin Tag.F4.rank → ℤ) = wordMat Tag.F4 TwClass.wordF4 *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec Tag.F4 TwClass.wordF4 x

end QuasiF4

theorem isQuasisimple_f4Six_X₁ {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    CFSG.IsQuasisimple ↥(TwClass.f4Six.X₁ D) := by
  obtain ⟨π, hπ⟩ := QuasiF4.long_graph
  refine D.isQuasisimple_frame ?_
  refine D.isQuasisimple_fixedRoot_A2Frame hK
    (h := (f4Long_frame (L := D.L)).transport f4LongV) QuasiF4.S₁_eq_chain π ?_
  intro i j hij
  show (QuasiF4.wF4 • (f4LongV • chainRoot f4chainLong i j) : Fin Tag.F4.rank → ℤ) =
    f4LongV • chainRoot f4chainLong (π j) (π i)
  rw [QuasiF4.w_smul, f4LongV_smul, f4LongV_smul]
  exact hπ i j hij

theorem isQuasisimple_f4Six_X₂ {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    CFSG.IsQuasisimple ↥(TwClass.f4Six.X₂ D) := by
  obtain ⟨π, hπ⟩ := QuasiF4.short_graph
  refine D.isQuasisimple_frame ?_
  refine D.isQuasisimple_fixedRoot_A2Frame hK (h := f4Short_frame (L := D.L))
    QuasiF4.S₂_eq_chain π ?_
  intro i j hij
  show (QuasiF4.wF4 • f4ShortSigma i j : Fin Tag.F4.rank → ℤ) = f4ShortSigma (π j) (π i)
  rw [QuasiF4.w_smul]
  exact hπ i j hij

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
