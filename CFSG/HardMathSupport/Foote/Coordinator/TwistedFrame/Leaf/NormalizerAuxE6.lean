module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxF4
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE (wordProd_smul_eq_wordMat_mulVec map_conj_rootSpan)

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chain13 chain56 support13 support56 supportA2A2 e6Index chainRoot chainRoot_swap
  e6RootVec isRoot_iff_exists_e6RootVec isRoot_e6RootVec mem_supportA2A2)

open CFSG.RankThree.PartOne.TCX.E (A2Std a2Std₁ a2Std₂ chainRoot_eq_weight_sub)

open Matrix
open scoped MatrixGroups Matrix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


set_option linter.unusedSectionVars false


@[expose] def e6ListS2 : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, 0, -1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0]]

@[expose] def e6ListS1 : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1], ![0, -1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def e6WordV : List (Fin Tag.E6.rank) := [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

theorem S₂_e6Six : TwClass.S₂ TwClass.e6Six = {r | r ∈ e6ListS2} := by
  ext α
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    have : ∀ m : Fin 72, (∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) →
        e6RootVec m i = 0) → e6RootVec m ∈ e6ListS2 := by decide +kernel
    exact this m hs
  · intro hr
    have : ∀ r ∈ e6ListS2, (∃ m : Fin 72, e6RootVec m = r) ∧
        ∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) → r i = 0 := by decide +kernel
    obtain ⟨⟨m, rfl⟩, hs⟩ := this α hr
    exact ⟨isRoot_e6RootVec m, hs⟩

theorem S₁_e6Six : TwClass.S₁ TwClass.e6Six = {r | r ∈ e6ListS1} := by
  ext β
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    rw [S₂_e6Six] at ho
    have : ∀ m : Fin 72, (∀ α ∈ e6ListS2, iform (τ := Tag.E6) (e6RootVec m) α = 0) →
        e6RootVec m ∈ e6ListS1 := by decide +kernel
    exact this m fun α hα => ho α hα
  · intro hr
    refine ⟨?_, fun α hα => ?_⟩
    · have : ∀ r ∈ e6ListS1, ∃ m : Fin 72, e6RootVec m = r := by decide +kernel
      obtain ⟨m, rfl⟩ := this β hr
      exact isRoot_e6RootVec m
    · rw [S₂_e6Six] at hα
      have : ∀ r ∈ e6ListS1, ∀ α ∈ e6ListS2, iform (τ := Tag.E6) r α = 0 := by decide +kernel
      exact this β hr α hα

@[expose] noncomputable def e6V : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6WordV

theorem e6V_smul (u : Fin Tag.E6.rank → ℤ) : e6V • u = wordMat Tag.E6 e6WordV *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec Tag.E6 e6WordV u

theorem e6_img : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j ∈ e6ListS1 := by decide +kernel

theorem e6_cover : ∀ r ∈ e6ListS1, ∃ i j : Fin 3, i ≠ j ∧
    r = wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j := by decide +kernel

theorem frameRoots_e6S1 :
    frameRoots (fun i j : Fin 3 => e6V • chainRoot chain13 i j) = {r | r ∈ e6ListS1} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    show e6V • chainRoot chain13 i j ∈ e6ListS1
    rw [e6V_smul]
    exact e6_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := e6_cover r hr
    exact ⟨i, j, hij, by show r = e6V • chainRoot chain13 i j; rw [e6V_smul]; exact h⟩

theorem w_e6Six_S1 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ (wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j) =
      wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem a2Std_isSLFrame {J : Set (Fin Tag.E6.rank)} {ι : Fin 2 → Fin Tag.E6.rank}
    (std : A2Std J ι) (L : Type) [Field L] (v : WeylGroup Tag.E6) :
    IsSLFrame (std.rhoV L v) (fun i j : Fin 3 => v • chainRoot ι i j) where
  isRoot i j hij := IsRoot.smul ((std.roots _).2 ⟨i, j, hij, rfl⟩).1 v
  neg i j := by rw [chainRoot_swap ι i j, smul_neg]
  add i j k := by
    rw [← smul_add, chainRoot_eq_weight_sub ι i j, chainRoot_eq_weight_sub ι j k,
      chainRoot_eq_weight_sub ι i k]
    congr 1
    abel
  transv i j hij := std.rhoV_transvection L v hij
  range := by
    rw [CFSG.RankThree.PartOne.TCX.E.A2Std.rhoV, MonoidHom.range_comp, std.range,
      subsystemGroup_eq_rootSpan, map_conj_rootSpan v (fun γ hγ => hγ.1)]
    congr 1
    ext r
    constructor
    · rintro ⟨α, hα, rfl⟩
      obtain ⟨i, j, hij, rfl⟩ := (std.roots α).1 hα
      exact ⟨i, j, hij, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨chainRoot ι i j, (std.roots _).2 ⟨i, j, hij, rfl⟩, rfl⟩

theorem e6Six_X₁ (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    CFSG.IsQuasisimple ↥(D.frame (TwClass.S₁ TwClass.e6Six)) ∧
      Group.IsSolvable (Outer ↥(D.frame (TwClass.S₁ TwClass.e6Six))) := by
  let r : Fin 3 → Fin 3 → Fin TwClass.e6Six.tag.rank → ℤ :=
    fun i j => e6V • chainRoot chain13 i j
  have hfr : IsSLFrame (τ := TwClass.e6Six.tag) (a2Std₁.rhoV D.L e6V) r :=
    a2Std_isSLFrame a2Std₁ D.L e6V
  have hinj : Function.Injective (a2Std₁.rhoV D.L e6V) :=
    (MulAut.conj _).injective.comp (a2Std₁.inj D.L)
  have hπ : ∀ i j : Fin 3, i ≠ j →
      TwClass.w TwClass.e6Six • r i j = r (Fin.revPerm j) (Fin.revPerm i) := by
    intro i j hij
    show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • (e6V • chainRoot chain13 i j) =
      e6V • chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i)
    rw [e6V_smul, e6V_smul, wordProd_smul_eq_wordMat_mulVec]
    exact w_e6Six_S1 i j hij
  have key := quasisimple_outer_solvable_fixedRoot_unitary D (ν := 3) le_rfl
    (fun h => by have := congrArg Prod.snd h; simp at this; omega) hfr hinj Fin.revPerm hπ
  have hS : frameRoots r = TwClass.S₁ TwClass.e6Six := frameRoots_e6S1.trans S₁_e6Six.symm
  rw [hS] at key
  exact quasisimple_outer_frame_of_fixedRoot D key

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
