module

public import CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
import all CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.TorusConjugation
public import CFSG.GroupTheory.CoprimeActionSupport.OddFieldSquareStableAdditive

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.RootIrreducible

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData
open CFSG.LinearAlgebra.ProjectiveRootSpaces.TorusConjugation
open CFSG.GroupTheory.CoprimeActionSupport.OddFieldSquareStableAdditive

variable {F : Type} [Field F]

theorem upperSubgroup_ne_bot : upperSubgroup F ≠ ⊥ := by
  intro h
  have hmem : upperPSL F (Multiplicative.ofAdd (1 : F)) ∈ upperSubgroup F := upperPSL_mem _
  rw [h, Subgroup.mem_bot] at hmem
  have := upperPSL_injective (hmem.trans (map_one (upperPSL F)).symm)
  exact one_ne_zero (α := F) (by simpa using this)

theorem isIrreducibleUnder_mono {G : Type} [Group G] {L L' V : Subgroup G} (h : L ≤ L')
    (hirr : CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder L V) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder L' V := by
  unfold CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder at *
  exact ⟨hirr.1, fun W hW hN => hirr.2 W hW (h.trans hN)⟩

@[expose] def rootAddSubgroup (W : Subgroup PSL(2, F)) : AddSubgroup F where
  carrier := {x | upperPSL F (Multiplicative.ofAdd x) ∈ W}
  zero_mem' := by simpa using W.one_mem
  add_mem' := by
    intro x y hx hy
    have := W.mul_mem hx hy
    simpa [ofAdd_add] using this
  neg_mem' := by
    intro x hx
    have := W.inv_mem hx
    simpa [ofAdd_neg] using this

theorem isIrreducibleUnder_torus (h2 : (2 : F) ≠ 0) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder (torus F) (upperSubgroup F) := by
  unfold CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
  refine ⟨upperSubgroup_ne_bot, ?_⟩
  intro W hWU hN
  have hsq : ∀ (a : Fˣ) (x : F), x ∈ rootAddSubgroup W → ((a : F) ^ 2) * x ∈ rootAddSubgroup W := by
    intro a x hx
    have hx' : upperPSL F (Multiplicative.ofAdd x) ∈ W := hx
    have hd := hN (diagonalPSL_mem a)
    rw [Subgroup.mem_normalizer_iff] at hd
    have := (hd _).mp hx'
    show upperPSL F (Multiplicative.ofAdd (((a : F) ^ 2) * x)) ∈ W
    rwa [← diagonalPSL_conj_upperPSL]
  by_cases hbot : rootAddSubgroup W = ⊥
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨b, rfl⟩ := hWU hw
    have : Multiplicative.toAdd b ∈ rootAddSubgroup W := by
      show upperPSL F (Multiplicative.ofAdd (Multiplicative.toAdd b)) ∈ W
      simpa using hw
    rw [hbot, AddSubgroup.mem_bot] at this
    have hb : b = 1 := by simpa using this
    simp [hb]
  · right
    have htop := eq_top_of_sq_stable h2 _ hsq hbot
    apply le_antisymm hWU
    rintro _ ⟨b, rfl⟩
    have : Multiplicative.toAdd b ∈ rootAddSubgroup W := by rw [htop]; trivial
    have h' : upperPSL F (Multiplicative.ofAdd (Multiplicative.toAdd b)) ∈ W := this
    simpa using h'

theorem isIrreducibleUnder_normalizer (h2 : (2 : F) ≠ 0) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
      (Subgroup.normalizer (upperSubgroup F : Set PSL(2, F))) (upperSubgroup F) :=
  isIrreducibleUnder_mono torus_le_normalizer_upperSubgroup (isIrreducibleUnder_torus h2)

end CFSG.LinearAlgebra.ProjectiveRootSpaces.RootIrreducible
