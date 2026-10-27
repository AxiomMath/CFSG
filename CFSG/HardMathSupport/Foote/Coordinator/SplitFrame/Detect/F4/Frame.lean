module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.OuterSL

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def S1set : Set (Fin Tag.F4.rank → ℤ) := {r | r ∈ f4LongList}

@[expose] def S2set : Set (Fin Tag.F4.rank → ℤ) := {r | r ∈ f4ShortList}

theorem exists_splitFrame_F4' (K : Type) [Field K] :
    ∃ (ψA ψB : SL(3, K) →* ModGL Tag.F4 K) (σA σB : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      IsA2Frame ψA σA ∧ IsA2Frame ψB σB ∧ (∀ A B, Commute (ψA A) (ψB B)) ∧
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = σA i j} = S1set ∧
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = σB i j} = S2set := by
  have hA := (f4Long_frame (L := K)).transport f4LongV
  have hB := f4Short_frame (L := K)
  have hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} =
      S1set := by
    ext r
    simp only [Set.mem_ofPred_eq, f4LongV_smul, S1set]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact long_img i j hij
    · intro hr
      obtain ⟨i, j, hij, h⟩ := long_cover r hr
      exact ⟨i, j, hij, h⟩
  have hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} = S2set := by
    ext r
    simp only [Set.mem_ofPred_eq, S2set]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact short_img i j hij
    · intro hr
      exact short_cover r hr
  have hrA := hA.range
  have hrB := hB.range
  rw [hSA] at hrA
  rw [hSB] at hrB
  have hcomm : ∀ u ∈ rootSpan Tag.F4 K S1set, ∀ v ∈ rootSpan Tag.F4 K S2set, u * v = v * u := by
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    obtain ⟨h0, hp⟩ := orth_list α hα β hβ
    obtain ⟨m, rfl⟩ := list_roots α (List.mem_append_left _ hα)
    obtain ⟨m', rfl⟩ := list_roots β (List.mem_append_right _ hβ)
    exact pinnedX_commute_of_iform_eq_zero K (isRoot_f4RootVec m) (isRoot_f4RootVec m') h0
      (fun hr => hp (isRoot_iff_exists_f4RootVec.1 hr)) c d
  refine ⟨_, _, _, _, hA, hB, fun A B => ?_, hSA, hSB⟩
  refine hcomm _ ?_ _ ?_
  · rw [← hrA]; exact ⟨A, rfl⟩
  · rw [← hrB]; exact ⟨B, rfl⟩

section Derived

variable (K : Type) [Field K]

abbrev X1 : Subgroup (ModGL Tag.F4 K) := rootSpan Tag.F4 K S1set

abbrev X2 : Subgroup (ModGL Tag.F4 K) := rootSpan Tag.F4 K S2set

abbrev XS : Subgroup (ModGL Tag.F4 K) := rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3)

theorem isRoot_of_mem_S1set {r : Fin Tag.F4.rank → ℤ} (hr : r ∈ S1set) : IsRoot Tag.F4 r := by
  obtain ⟨m, rfl⟩ := list_roots r (List.mem_append_left _ hr)
  exact isRoot_f4RootVec m

theorem isRoot_of_mem_S2set {r : Fin Tag.F4.rank → ℤ} (hr : r ∈ S2set) : IsRoot Tag.F4 r := by
  obtain ⟨m, rfl⟩ := list_roots r (List.mem_append_right _ hr)
  exact isRoot_f4RootVec m

theorem XS_eq : XS K = X1 K ⊔ X2 K := by
  rw [XS, coset_eq, ← rootSpan_union_eq]
  rfl

theorem X1_le_XS : X1 K ≤ XS K := by rw [XS_eq]; exact le_sup_left

theorem X2_le_XS : X2 K ≤ XS K := by rw [XS_eq]; exact le_sup_right

theorem X1_X2_commute : ∀ x ∈ X1 K, ∀ y ∈ X2 K, x * y = y * x := by
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hcomm, hSA, hSB⟩ := exists_splitFrame_F4' K
  have hrA := hA.range
  have hrB := hB.range
  rw [hSA] at hrA
  rw [hSB] at hrB
  intro x hx y hy
  have hx' : x ∈ rootSpan Tag.F4 K S1set := hx
  have hy' : y ∈ rootSpan Tag.F4 K S2set := hy
  rw [← hrA] at hx'
  rw [← hrB] at hy'
  obtain ⟨A, rfl⟩ := hx'
  obtain ⟨B, rfl⟩ := hy'
  exact hcomm A B

theorem X1_perfect : ⁅X1 K, X1 K⁆ = X1 K := by
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hcomm, hSA, hSB⟩ := exists_splitFrame_F4' K
  have hrA := hA.range
  rw [hSA] at hrA
  show ⁅rootSpan Tag.F4 K S1set, rootSpan Tag.F4 K S1set⁆ = rootSpan Tag.F4 K S1set
  rw [← hrA]
  have hperf := (isQuasisimple_SL (K := K) (n := 3) (by norm_num)).1
  have h1 : (⁅(⊤ : Subgroup SL(3, K)), (⊤ : Subgroup SL(3, K))⁆) = ⊤ := by
    have := hperf.commutator_eq_top
    rwa [_root_.commutator_def] at this
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

theorem X2_quasisimple : CFSG.IsQuasisimple (X2 K) := by
  obtain ⟨ψA, ψB, σA, σB, hA, hB, hcomm, hSA, hSB⟩ := exists_splitFrame_F4' K
  have hrB := hB.range
  rw [hSB] at hrB
  show CFSG.IsQuasisimple (rootSpan Tag.F4 K S2set)
  rw [← hrB]
  exact (isQuasisimple_SL (K := K) (n := 3) (by norm_num)).of_mulEquiv
    (MonoidHom.ofInjective hB.injective).symm

end Derived

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
