module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.OuterSL
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem exists_splitFrame_E8' (K : Type) [Field K] :
    ∃ ψ₁ ψ₂ : SL(5, K) →* ModGL Tag.E8 K,
      Function.Injective ψ₁ ∧ Function.Injective ψ₂ ∧ (∀ A B, Commute (ψ₁ A) (ψ₂ B)) ∧
      ψ₁.range = rootSpan Tag.E8 K S1set ∧ ψ₂.range = rootSpan Tag.E8 K S2set := by
  have hSA : sigmaSetE8A4 e8VA = {r | r ∈ e8ListA} := by
    rw [sigmaSetE8A4_eq]
    ext r
    simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VA_smul]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact e8A_img i j hij
    · intro hr
      exact e8A_cover r hr
  have hSB : sigmaSetE8A4 e8VB = {r | r ∈ e8ListB} := by
    rw [sigmaSetE8A4_eq]
    ext r
    simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VB_smul]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact e8B_img i j hij
    · intro hr
      exact e8B_cover r hr
  have hrA := rhoSigmaE8A4_range (L := K) e8VA
  have hrB := rhoSigmaE8A4_range (L := K) e8VB
  rw [hSA] at hrA
  rw [hSB] at hrB
  have hcomm : ∀ u ∈ rootSpan Tag.E8 K {r | r ∈ e8ListB},
      ∀ v ∈ rootSpan Tag.E8 K {r | r ∈ e8ListA}, u * v = v * u := by
    intro u hu v hv
    refine (rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl))) ?_ ?_ ?_ v hv u hu).symm
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_left _ hr)
      exact isRoot_e8RootVec m
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_right _ hr)
      exact isRoot_e8RootVec m
    · intro α hα β hβ
      exact e8_orth α hα β hβ
  refine ⟨rhoSigmaE8A4 K e8VB, rhoSigmaE8A4 K e8VA, rhoSigmaE8A4_injective e8VB,
    rhoSigmaE8A4_injective e8VA, fun A B => ?_, hrB, hrA⟩
  refine hcomm _ ?_ _ ?_
  · rw [← hrB]; exact ⟨A, rfl⟩
  · rw [← hrA]; exact ⟨B, rfl⟩

section Derived

variable (K : Type) [Field K]

abbrev X1 : Subgroup (ModGL Tag.E8 K) := rootSpan Tag.E8 K S1set

abbrev X2 : Subgroup (ModGL Tag.E8 K) := rootSpan Tag.E8 K S2set

abbrev XS : Subgroup (ModGL Tag.E8 K) := rootSpan Tag.E8 K (cosetRoots Tag.E8 4 5)

theorem isRoot_of_mem_S1set {r : Fin Tag.E8.rank → ℤ} (hr : r ∈ S1set) : IsRoot Tag.E8 r := by
  obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_right _ hr)
  exact isRoot_e8RootVec m

theorem isRoot_of_mem_S2set {r : Fin Tag.E8.rank → ℤ} (hr : r ∈ S2set) : IsRoot Tag.E8 r := by
  obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_left _ hr)
  exact isRoot_e8RootVec m

theorem XS_eq : XS K = X1 K ⊔ X2 K := by
  rw [XS, e8_coset_eq, Set.union_comm, ← rootSpan_union_eq]
  rfl

theorem X1_le_XS : X1 K ≤ XS K := by rw [XS_eq]; exact le_sup_left

theorem X2_le_XS : X2 K ≤ XS K := by rw [XS_eq]; exact le_sup_right

theorem X1_X2_commute : ∀ x ∈ X1 K, ∀ y ∈ X2 K, x * y = y * x := by
  obtain ⟨ψ₁, ψ₂, h₁, h₂, hcomm, hr₁, hr₂⟩ := exists_splitFrame_E8' K
  intro x hx y hy
  have hx' : x ∈ rootSpan Tag.E8 K S1set := hx
  have hy' : y ∈ rootSpan Tag.E8 K S2set := hy
  rw [← hr₁] at hx'
  rw [← hr₂] at hy'
  obtain ⟨A, rfl⟩ := hx'
  obtain ⟨B, rfl⟩ := hy'
  exact hcomm A B

theorem X1_perfect : ⁅X1 K, X1 K⁆ = X1 K := by
  obtain ⟨ψ₁, ψ₂, h₁, h₂, hcomm, hr₁, hr₂⟩ := exists_splitFrame_E8' K
  show ⁅rootSpan Tag.E8 K S1set, rootSpan Tag.E8 K S1set⁆ = rootSpan Tag.E8 K S1set
  rw [← hr₁]
  have hperf := (isQuasisimple_SL (K := K) (n := 5) (by norm_num)).1
  have h1 : (⁅(⊤ : Subgroup SL(5, K)), (⊤ : Subgroup SL(5, K))⁆) = ⊤ := by
    have := hperf.commutator_eq_top
    rwa [_root_.commutator_def] at this
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

theorem X2_quasisimple : CFSG.IsQuasisimple (X2 K) := by
  obtain ⟨ψ₁, ψ₂, h₁, h₂, hcomm, hr₁, hr₂⟩ := exists_splitFrame_E8' K
  show CFSG.IsQuasisimple (rootSpan Tag.E8 K S2set)
  rw [← hr₂]
  exact (isQuasisimple_SL (K := K) (n := 5) (by norm_num)).of_mulEquiv
    (MonoidHom.ofInjective h₂).symm

end Derived

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
