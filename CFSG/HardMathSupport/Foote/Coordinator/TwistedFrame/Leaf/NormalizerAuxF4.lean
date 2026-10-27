module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxOut
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KF4
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6 CFSG.RankThree.Lattice
open Matrix
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


theorem S₂_f4Six : TwClass.S₂ TwClass.f4Six = {r | r ∈ f4ShortList} := by
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    have : ∀ m : Fin 48, (∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) → f4RootVec m i = 0) →
        f4RootVec m ∈ f4ShortList := by decide +kernel
    exact this m hs
  · intro hr
    have : ∀ r ∈ f4ShortList, (∃ m : Fin 48, f4RootVec m = r) ∧
        ∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) → r i = 0 := by decide +kernel
    obtain ⟨⟨m, rfl⟩, hs⟩ := this α hr
    exact ⟨isRoot_f4RootVec m, hs⟩


theorem S₁_f4Six : TwClass.S₁ TwClass.f4Six = {r | r ∈ f4LongList} := by
  ext β
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    rw [S₂_f4Six] at ho
    have : ∀ m : Fin 48, (∀ α ∈ f4ShortList, iform (τ := Tag.F4) (f4RootVec m) α = 0) →
        f4RootVec m ∈ f4LongList := by decide +kernel
    exact this m fun α hα => ho α hα
  · intro hr
    refine ⟨?_, fun α hα => ?_⟩
    · have : ∀ r ∈ f4LongList, ∃ m : Fin 48, f4RootVec m = r := by decide +kernel
      obtain ⟨m, rfl⟩ := this β hr
      exact isRoot_f4RootVec m
    · rw [S₂_f4Six] at hα
      exact (orth_list β hr α hα).1

theorem w_f4Six_long : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ (wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j) =
      wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong ((Equiv.swap (0 : Fin 3) 2) j)
        ((Equiv.swap (0 : Fin 3) 2) i) := by
  decide +kernel

theorem w_f4Six_short : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ f4ShortSigma i j =
      f4ShortSigma ((Equiv.swap (0 : Fin 3) 2) j) ((Equiv.swap (0 : Fin 3) 2) i) := by
  decide +kernel


open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem quasisimple_outer_frame_of_fixedRoot {τ : Tag} {K : Type} [Field K] [Finite K]
    {w : WeylGroup τ} (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)}
    (h : CFSG.IsQuasisimple ↥(fixedRoot D S) ∧ Group.IsSolvable (Outer ↥(fixedRoot D S))) :
    CFSG.IsQuasisimple ↥(D.frame S) ∧ Group.IsSolvable (Outer ↥(D.frame S)) := by
  have e := frameEquivFixedRoot D h.1.1
  haveI := h.2
  exact ⟨CFSG.IsQuasisimple.of_mulEquiv e h.1, CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm⟩

theorem frameRoots_f4Long :
    frameRoots (fun i j : Fin 3 => f4LongV • chainRoot f4chainLong i j) =
      {r | r ∈ f4LongList} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    show f4LongV • chainRoot f4chainLong i j ∈ f4LongList
    rw [f4LongV_smul]
    exact long_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := long_cover r hr
    exact ⟨i, j, hij, by show r = f4LongV • chainRoot f4chainLong i j; rw [f4LongV_smul]; exact h⟩

theorem frameRoots_f4Short :
    frameRoots (fun i j : Fin 3 => f4ShortSigma i j) = {r | r ∈ f4ShortList} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact short_img i j hij
  · intro hr
    exact short_cover r hr

theorem f4Six_X₁ (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₁ TwClass.f4Six)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₁ TwClass.f4Six))) := by
  let r₁ : Fin 3 → Fin 3 → Fin TwClass.f4Six.tag.rank → ℤ :=
    fun i j => f4LongV • chainRoot f4chainLong i j
  have hfr : IsSLFrame (τ := TwClass.f4Six.tag)
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) D.L f4LongV)).toMonoidHom.comp
        (f4rhoLong D.L)) r₁ :=
    IsSLFrame.of_isA2Frame ((f4Long_frame (L := D.L)).transport f4LongV)
  have hinj := ((f4Long_frame (L := D.L)).transport f4LongV).injective
  have hπ : ∀ i j : Fin 3, i ≠ j →
      TwClass.w TwClass.f4Six • r₁ i j = r₁ ((Equiv.swap (0 : Fin 3) 2) j) ((Equiv.swap (0 : Fin 3) 2) i) := by
    intro i j hij
    show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • (f4LongV • chainRoot f4chainLong i j) =
      f4LongV • chainRoot f4chainLong ((Equiv.swap (0 : Fin 3) 2) j) ((Equiv.swap (0 : Fin 3) 2) i)
    rw [f4LongV_smul, f4LongV_smul, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    exact w_f4Six_long i j hij
  have key := quasisimple_outer_solvable_fixedRoot_unitary D (ν := 3) le_rfl
    (fun h => by have := congrArg Prod.snd h; simp at this; omega) hfr hinj (Equiv.swap 0 2) hπ
  have hS : frameRoots r₁ = TwClass.S₁ TwClass.f4Six := frameRoots_f4Long.trans S₁_f4Six.symm
  rw [hS] at key
  exact quasisimple_outer_frame_of_fixedRoot D key

theorem f4Six_X₂ (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₂ TwClass.f4Six)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₂ TwClass.f4Six))) := by
  let r₂ : Fin 3 → Fin 3 → Fin TwClass.f4Six.tag.rank → ℤ := fun i j => f4ShortSigma i j
  have hfr : IsSLFrame (τ := TwClass.f4Six.tag) (f4rhoShort D.L) r₂ :=
    IsSLFrame.of_isA2Frame (f4Short_frame (L := D.L))
  have hinj := (f4Short_frame (L := D.L)).injective
  have hπ : ∀ i j : Fin 3, i ≠ j →
      TwClass.w TwClass.f4Six • r₂ i j = r₂ ((Equiv.swap (0 : Fin 3) 2) j) ((Equiv.swap (0 : Fin 3) 2) i) := by
    intro i j hij
    show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • f4ShortSigma i j =
      f4ShortSigma ((Equiv.swap (0 : Fin 3) 2) j) ((Equiv.swap (0 : Fin 3) 2) i)
    rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    exact w_f4Six_short i j hij
  have key := quasisimple_outer_solvable_fixedRoot_unitary D (ν := 3) le_rfl
    (fun h => by have := congrArg Prod.snd h; simp at this; omega) hfr hinj (Equiv.swap 0 2) hπ
  have hS : frameRoots r₂ = TwClass.S₂ TwClass.f4Six := frameRoots_f4Short.trans S₂_f4Six.symm
  rw [hS] at key
  exact quasisimple_outer_frame_of_fixedRoot D key

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
