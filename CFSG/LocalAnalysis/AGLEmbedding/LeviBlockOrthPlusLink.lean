module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMaxBorel

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def plusNodeSpace (hr : 3 ≤ r) (i : Fin r) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  if i.val + 1 ≤ r - 2 then flag r K (i.val + 1)
  else if i.val = r - 2 then Xstar r K (by omega) else flag r K r

variable (K) in
@[expose] noncomputable def plusNodeStab (hr : 3 ≤ r) (I : Set (Fin r)) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  orthElementaryGroup (quadPlus r K) ⊓
    ⨅ i ∈ I, MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
      (plusNodeSpace K hr i)

theorem mem_plusNodeStab {hr : 3 ≤ r} {I : Set (Fin r)}
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ plusNodeStab K hr I ↔ g ∈ orthElementaryGroup (quadPlus r K) ∧
      ∀ i ∈ I, g • plusNodeSpace K hr i = plusNodeSpace K hr i := by
  simp only [plusNodeStab, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem plusNodeStab_le (hr : 3 ≤ r) (I : Set (Fin r)) :
    plusNodeStab K hr I ≤ orthElementaryGroup (quadPlus r K) :=
  inf_le_left

theorem plusNodeStab_empty (hr : 3 ≤ r) :
    plusNodeStab K hr (∅ : Set (Fin r)) = orthElementaryGroup (quadPlus r K) := by
  ext g
  simp [mem_plusNodeStab]

theorem borel_le_stabilizer_plusNodeSpace (hr : 3 ≤ r) (i : Fin r) :
    borel r K ≤ MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
      (plusNodeSpace K hr i) := by
  unfold plusNodeSpace
  split_ifs with h1 h2
  · exact borel_le_stabilizer_flag (by omega) (by omega)
  · exact borel_le_stabilizer_Xstar _
  · exact borel_le_stabilizer_flag (by omega) le_rfl

theorem borel_le_plusNodeStab (hr : 3 ≤ r) (I : Set (Fin r)) : borel r K ≤ plusNodeStab K hr I :=
  fun _ hb => mem_plusNodeStab.2 ⟨borel_le hb, fun i _ =>
    MulAction.mem_stabilizer_iff.1 (borel_le_stabilizer_plusNodeSpace hr i hb)⟩

theorem weylElt_smul_plusNodeSpace_of_ne (hr : 3 ≤ r) {i j : Fin r} (hji : j ≠ i) :
    weylElt r K j • plusNodeSpace K hr i = plusNodeSpace K hr i := by
  have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have hj := j.isLt
  have hi := i.isLt
  unfold plusNodeSpace
  split_ifs with h1 h2
  · exact weylElt_smul_flag_of_ne hr (by omega) h1 (by omega)
  · by_cases hj2 : j.val + 1 ≤ r - 2
    · exact (weylElt_smul_flag_top_and_Xstar hr hj2).2
    · rw [show j = ⟨r - 1, by omega⟩ from Fin.ext (by simp only; omega)]
      exact (weylElt_last_smul hr).2
  · by_cases hj2 : j.val + 1 ≤ r - 2
    · exact (weylElt_smul_flag_top_and_Xstar hr hj2).1
    · rw [show j = ⟨r - 2, by omega⟩ from Fin.ext (by simp only; omega)]
      exact (weylElt_penult_smul hr).2

theorem weylElt_smul_plusNodeSpace_self (hr : 3 ≤ r) (i : Fin r) :
    weylElt r K i • plusNodeSpace K hr i ≠ plusNodeSpace K hr i := by
  have hi := i.isLt
  unfold plusNodeSpace
  split_ifs with h1 h2
  · exact weylElt_smul_flag_ne hr h1
  · rw [show i = ⟨r - 2, by omega⟩ from Fin.ext h2]
    exact (weylElt_penult_smul hr).1
  · rw [show i = ⟨r - 1, by omega⟩ from Fin.ext (by simp only; omega)]
    exact (weylElt_last_smul hr).1

theorem weylElt_mem_plusNodeStab_iff (hr : 3 ≤ r) (I : Set (Fin r)) (i : Fin r) :
    weylElt r K i ∈ plusNodeStab K hr I ↔ i ∉ I := by
  rw [mem_plusNodeStab]
  constructor
  · rintro ⟨-, h⟩ hi
    exact weylElt_smul_plusNodeSpace_self hr i (h i hi)
  · intro hi
    refine ⟨weylElt_mem i, fun j hj => weylElt_smul_plusNodeSpace_of_ne hr fun h => ?_⟩
    subst h
    exact hi hj

theorem plusNodeStab_generation (hr : 3 ≤ r) (I : Set (Fin r)) :
    plusNodeStab K hr I = Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K]
      (Fin r ⊕ Fin r → K))) ∪ weylElt r K '' Iᶜ) ∧
    ∀ i, weylElt r K i ∈ plusNodeStab K hr I ↔ i ∉ I := by
  refine ⟨(eq_closure_of_borel_le hr (plusNodeStab_le hr I) (borel_le_plusNodeStab hr I)).trans
    ?_, weylElt_mem_plusNodeStab_iff hr I⟩
  congr 3
  ext i
  exact weylElt_mem_plusNodeStab_iff hr I i

theorem eq_plusNodeStab_of_borel_le (hr : 3 ≤ r)
    {M : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))}
    (hMG : M ≤ orthElementaryGroup (quadPlus r K)) (hBM : borel r K ≤ M) :
    M = plusNodeStab K hr {i | weylElt r K i ∉ M} := by
  refine le_antisymm ((eq_closure_of_borel_le hr hMG hBM).le.trans
    ((Subgroup.closure_le _).2 ?_)) ?_
  · rintro _ (hb | ⟨j, hj, rfl⟩)
    · exact borel_le_plusNodeStab hr _ hb
    · exact (weylElt_mem_plusNodeStab_iff hr _ j).2 fun h => h hj
  · rw [(plusNodeStab_generation hr _).1, Subgroup.closure_le]
    rintro _ (hb | ⟨j, hj, rfl⟩)
    · exact hBM hb
    · simpa using hj

end CFSG.AGLEmbedding.LeviBlock
