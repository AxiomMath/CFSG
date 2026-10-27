module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KF4.ShortA2Frame
public import CFSG.RankThree.PartOne.KE.E8A4Sigma
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def f4LongWord : List (Fin Tag.F4.rank) := [1, 2, 0, 1, 2, 3, 0, 1, 2]

@[expose] noncomputable def f4LongV : WeylGroup Tag.F4 := (coxeterSystem Tag.F4).wordProd f4LongWord

@[expose] def f4LongList : List (Fin Tag.F4.rank → ℤ) :=
  [![1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 3, 4, 2], ![-1, -3, -4, -2], ![2, 3, 4, 2], ![-2, -3, -4, -2]]

@[expose] def f4ShortList : List (Fin Tag.F4.rank → ℤ) :=
  [![0, 0, 1, 0], ![0, 0, -1, 0], ![0, 0, 0, 1], ![0, 0, 0, -1], ![0, 0, 1, 1], ![0, 0, -1, -1]]

theorem f4LongV_smul (u : Fin Tag.F4.rank → ℤ) :
    f4LongV • u = wordMat Tag.F4 f4LongWord *ᵥ u := by
  rw [f4LongV, wordProd_smul_eq_wordMat_mulVec]

theorem long_img : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j ∈ f4LongList := by
  decide +kernel

theorem long_cover : ∀ r ∈ f4LongList, ∃ i j : Fin 3, i ≠ j ∧
    r = wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j := by
  decide +kernel

theorem short_img : ∀ i j : Fin 3, i ≠ j → f4ShortSigma i j ∈ f4ShortList := by
  decide +kernel

theorem short_cover : ∀ r ∈ f4ShortList, ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j := by
  decide +kernel

theorem coset_sub : ∀ m : Fin 48, (f4RootVec m (1 : Fin Tag.F4.rank)) % 3 = 0 →
    f4RootVec m ∈ f4LongList ∨ f4RootVec m ∈ f4ShortList := by
  decide +kernel

theorem list_roots : ∀ r ∈ f4LongList ++ f4ShortList, ∃ m : Fin 48, f4RootVec m = r := by
  decide +kernel


theorem orth_list : ∀ α ∈ f4LongList, ∀ β ∈ f4ShortList,
    iform (τ := Tag.F4) α β = 0 ∧ ¬ ∃ m : Fin 48, f4RootVec m = α + β := by
  decide +kernel

theorem rootSpan_union_eq {τ : Tag} {K : Type} [Field K] (A B : Set (Fin τ.rank → ℤ)) :
    rootSpan τ K (A ∪ B) = rootSpan τ K A ⊔ rootSpan τ K B := by
  simp only [rootSpan]
  exact iSup_union

theorem rootSpan_commute_of_gen' {τ : Tag} {K : Type} [Field K] {S₁ S₂ : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ S₁, ∀ β ∈ S₂, ∀ c d : K,
      pinnedX τ K α c * pinnedX τ K β d = pinnedX τ K β d * pinnedX τ K α c) :
    ∀ u ∈ rootSpan τ K S₁, ∀ v ∈ rootSpan τ K S₂, u * v = v * u := by
  have hle : rootSpan τ K S₁ ≤ Subgroup.centralizer (rootSpan τ K S₂ : Set (ModGL τ K)) := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    have hle2 : rootSpan τ K S₂ ≤ Subgroup.centralizer ({pinnedX τ K α c} : Set (ModGL τ K)) := by
      refine iSup₂_le fun β hβ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨d, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h α hα β hβ c d).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle2 hv)
  intro u hu v hv
  exact (Subgroup.mem_centralizer_iff.1 (hle hu) v hv).symm

theorem coset_sup : ∀ m : Fin 48, f4RootVec m ∈ f4LongList ++ f4ShortList →
    (3 : ℤ) ∣ f4RootVec m (1 : Fin Tag.F4.rank) := by
  decide +kernel

theorem coset_eq : cosetRoots Tag.F4 1 3 = {r | r ∈ f4LongList} ∪ {r | r ∈ f4ShortList} := by
  ext r
  constructor
  · rintro ⟨hr, hd⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    have : (f4RootVec m (1 : Fin Tag.F4.rank)) % 3 = 0 := Int.emod_eq_zero_of_dvd hd
    exact coset_sub m this
  · intro hr
    have hr' : r ∈ f4LongList ++ f4ShortList := by
      rcases hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h
    obtain ⟨m, rfl⟩ := list_roots r hr'
    exact ⟨isRoot_f4RootVec m, coset_sup m hr'⟩

theorem exists_splitFrame_F4 (K : Type) [Field K] :
    ∃ ψA ψB : SL(3, K) →* ModGL Tag.F4 K,
      Function.Injective ψA ∧ Function.Injective ψB ∧ (∀ A B, Commute (ψA A) (ψB B)) ∧
      ψA.range ⊔ ψB.range = rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) := by
  have hA := (f4Long_frame (L := K)).transport f4LongV
  have hB := f4Short_frame (L := K)
  have hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} =
      {r | r ∈ f4LongList} := by
    ext r
    simp only [Set.mem_ofPred_eq, f4LongV_smul]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact long_img i j hij
    · intro hr
      obtain ⟨i, j, hij, h⟩ := long_cover r hr
      exact ⟨i, j, hij, h⟩
  have hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} = {r | r ∈ f4ShortList} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact short_img i j hij
    · intro hr
      exact short_cover r hr
  have hrA := hA.range
  have hrB := hB.range
  rw [hSA] at hrA
  rw [hSB] at hrB
  have hcomm : ∀ u ∈ rootSpan Tag.F4 K {r | r ∈ f4LongList},
      ∀ v ∈ rootSpan Tag.F4 K {r | r ∈ f4ShortList}, u * v = v * u := by
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    obtain ⟨h0, hp⟩ := orth_list α hα β hβ
    obtain ⟨m, rfl⟩ := list_roots α (List.mem_append_left _ hα)
    obtain ⟨m', rfl⟩ := list_roots β (List.mem_append_right _ hβ)
    exact pinnedX_commute_of_iform_eq_zero K (isRoot_f4RootVec m) (isRoot_f4RootVec m') h0
      (fun hr => hp (isRoot_iff_exists_f4RootVec.1 hr)) c d
  refine ⟨(MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K f4LongV)).toMonoidHom.comp
    (f4rhoLong K), f4rhoShort K, hA.injective, hB.injective, fun A B => ?_, ?_⟩
  · refine hcomm _ ?_ _ ?_
    · rw [← hrA]; exact ⟨A, rfl⟩
    · rw [← hrB]; exact ⟨B, rfl⟩
  · rw [hrA, hrB, coset_eq, rootSpan_union_eq]

section E8


@[expose] def e8WordA : List (Fin Tag.E8.rank) := [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]

@[expose] def e8WordB : List (Fin Tag.E8.rank) :=
  [4, 5, 6, 7, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 1]

@[expose] noncomputable def e8VA : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8WordA

@[expose] noncomputable def e8VB : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8WordB

@[expose] def e8ListA : List (Fin Tag.E8.rank → ℤ) :=
  [![-1, -1, -1, -1, 0, 0, 0, 0], ![-1, 0, -1, -1, 0, 0, 0, 0], ![-1, 0, -1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0]]

@[expose] def e8ListB : List (Fin Tag.E8.rank → ℤ) :=
  [![-2, -3, -4, -6, -5, -4, -3, -2], ![-2, -3, -4, -6, -5, -4, -3, -1], ![-2, -3, -4, -6, -5, -4, -2, -1], ![-2, -3, -4, -6, -5, -3, -2, -1], ![0, 0, 0, 0, 0, -1, -1, -1], ![0, 0, 0, 0, 0, -1, -1, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 1, 1], ![2, 3, 4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem e8VA_smul (u : Fin Tag.E8.rank → ℤ) : e8VA • u = wordMat Tag.E8 e8WordA *ᵥ u := by
  rw [e8VA, wordProd_smul_eq_wordMat_mulVec]

theorem e8VB_smul (u : Fin Tag.E8.rank → ℤ) : e8VB • u = wordMat Tag.E8 e8WordB *ᵥ u := by
  rw [e8VB, wordProd_smul_eq_wordMat_mulVec]

theorem e8A_img : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j ∈ e8ListA := by
  decide +kernel

theorem e8A_cover : ∀ r ∈ e8ListA, ∃ i j : Fin 5, i ≠ j ∧
    r = wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j := by
  decide +kernel

theorem e8B_img : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j ∈ e8ListB := by
  decide +kernel

theorem e8B_cover : ∀ r ∈ e8ListB, ∃ i j : Fin 5, i ≠ j ∧
    r = wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j := by
  decide +kernel

theorem e8_coset_sub : ∀ m : Fin 240, (e8RootVec m (4 : Fin Tag.E8.rank)) % 5 = 0 →
    e8RootVec m ∈ e8ListA ∨ e8RootVec m ∈ e8ListB := by
  decide +kernel

theorem e8_coset_sup : ∀ m : Fin 240, e8RootVec m ∈ e8ListA ++ e8ListB →
    (5 : ℤ) ∣ e8RootVec m (4 : Fin Tag.E8.rank) := by
  decide +kernel

theorem e8_list_roots : ∀ r ∈ e8ListA ++ e8ListB, ∃ m : Fin 240, e8RootVec m = r := by
  decide +kernel

theorem e8_orth : ∀ α ∈ e8ListA, ∀ β ∈ e8ListB,
    α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0 := by
  decide +kernel

theorem e8_coset_eq : cosetRoots Tag.E8 4 5 = {r | r ∈ e8ListA} ∪ {r | r ∈ e8ListB} := by
  ext r
  constructor
  · rintro ⟨hr, hd⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    have : (e8RootVec m (4 : Fin Tag.E8.rank)) % 5 = 0 := Int.emod_eq_zero_of_dvd hd
    exact e8_coset_sub m this
  · intro hr
    have hr' : r ∈ e8ListA ++ e8ListB := by
      rcases hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h
    obtain ⟨m, rfl⟩ := e8_list_roots r hr'
    exact ⟨isRoot_e8RootVec m, e8_coset_sup m hr'⟩

theorem exists_splitFrame_E8 (K : Type) [Field K] :
    ∃ ψA ψB : SL(5, K) →* ModGL Tag.E8 K,
      Function.Injective ψA ∧ Function.Injective ψB ∧ (∀ A B, Commute (ψA A) (ψB B)) ∧
      ψA.range ⊔ ψB.range = rootSpan Tag.E8 K (cosetRoots Tag.E8 4 5) := by
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
  have hcomm : ∀ u ∈ rootSpan Tag.E8 K {r | r ∈ e8ListA},
      ∀ v ∈ rootSpan Tag.E8 K {r | r ∈ e8ListB}, u * v = v * u := by
    refine rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl))) ?_ ?_ ?_
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_left _ hr)
      exact isRoot_e8RootVec m
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_right _ hr)
      exact isRoot_e8RootVec m
    · intro α hα β hβ
      exact e8_orth α hα β hβ
  refine ⟨rhoSigmaE8A4 K e8VA, rhoSigmaE8A4 K e8VB, rhoSigmaE8A4_injective e8VA,
    rhoSigmaE8A4_injective e8VB, fun A B => ?_, ?_⟩
  · refine hcomm _ ?_ _ ?_
    · rw [← hrA]; exact ⟨A, rfl⟩
    · rw [← hrB]; exact ⟨B, rfl⟩
  · rw [hrA, hrB, e8_coset_eq, rootSpan_union_eq]

end E8

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
