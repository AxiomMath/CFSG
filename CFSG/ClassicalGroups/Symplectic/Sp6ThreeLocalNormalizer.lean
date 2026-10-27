module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalDefs
public import CFSG.GroupTheory.SignedPermFixedSpace

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra CFSG.GroupTheory
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def blockVec (w : Fin 3 ⊕ Fin 3 → K) (i : Fin 3) : Fin 2 → K :=
  ![w (Sum.inl i), w (Sum.inr i)]

theorem blockVec_blockMatrix_mulVec (g : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (w : Fin 3 ⊕ Fin 3 → K) (i : Fin 3) :
    blockVec (blockMatrix g *ᵥ w) i = g i *ᵥ blockVec w i := by
  have h1 : (blockMatrix g *ᵥ w) (Sum.inl i) =
      g i 0 0 * w (Sum.inl i) + g i 0 1 * w (Sum.inr i) := by
    rw [blockMatrix, fromBlocks_mulVec]
    simp [Function.comp_apply, mulVec_diagonal]
  have h2 : (blockMatrix g *ᵥ w) (Sum.inr i) =
      g i 1 0 * w (Sum.inl i) + g i 1 1 * w (Sum.inr i) := by
    rw [blockMatrix, fromBlocks_mulVec]
    simp [Function.comp_apply, mulVec_diagonal]
  funext a
  fin_cases a
  · simpa [blockVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  · simpa [blockVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2

theorem eq_zero_of_forall_blockVec_eq_zero {w : Fin 3 ⊕ Fin 3 → K}
    (h : ∀ i, blockVec w i = 0) : w = 0 := by
  funext x
  rcases x with i | i
  · have h0 := congrFun (h i) 0
    simpa [blockVec] using h0
  · have h1 := congrFun (h i) 1
    simpa [blockVec] using h1

theorem mem_fixedVectors_c₀_iff {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (v : Multiplicative (Fin 3 → ZMod 3)) (w : Fin 3 ⊕ Fin 3 → K) :
    w ∈ fixedVectors ((StatedSp 3 K).subtype (c₀ hs v)) ↔
      ∀ i, ((s ^ (Multiplicative.toAdd v i).val : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        blockVec w i = blockVec w i := by
  have hm : (((StatedSp 3 K).subtype (c₀ hs v) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      blockMatrix (fun i => ((s ^ (Multiplicative.toAdd v i).val : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K)) := by
    rw [Subgroup.subtype_apply, c₀_apply hs v, coe_block]
  simp only [fixedVectors, Set.mem_setOf_eq]
  rw [hm]
  constructor
  · intro h i
    have h1 := congrArg (fun u => blockVec u i) h
    rwa [blockVec_blockMatrix_mulVec] at h1
  · intro h
    funext z
    rcases z with i | i
    · have hi : blockVec (blockMatrix (fun i => ((s ^ (Multiplicative.toAdd v i).val :
          SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *ᵥ w) i = blockVec w i := by
        rw [blockVec_blockMatrix_mulVec, h i]
      simpa [blockVec] using congrFun hi 0
    · have hi : blockVec (blockMatrix (fun i => ((s ^ (Multiplicative.toAdd v i).val :
          SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *ᵥ w) i = blockVec w i := by
        rw [blockVec_blockMatrix_mulVec, h i]
      simpa [blockVec] using congrFun hi 1

theorem commonFixedVectors_c₀_eq {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    commonFixedVectors (StatedSp 3 K).subtype (c₀ hs) = {0} := by
  ext w
  constructor
  · intro hw
    rw [Set.mem_singleton_iff]
    apply eq_zero_of_forall_blockVec_eq_zero
    intro i
    have hi : (s : Matrix (Fin 2) (Fin 2) K) *ᵥ blockVec w i = blockVec w i := by
      have h := (mem_fixedVectors_c₀_iff hs (Multiplicative.ofAdd (Pi.single i 1)) w).mp
        (Set.mem_iInter.mp (by simpa only [commonFixedVectors] using hw)
          (Multiplicative.ofAdd (Pi.single i 1))) i
      have h1 : ((1 : ZMod 3)).val = 1 := by decide
      simpa only [toAdd_ofAdd, Pi.single_eq_same, h1, pow_one] using h
    exact hs.eq_zero_of_mulVec_pow_eq (k := 1) (by norm_num) (by simpa using hi)
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    simp [commonFixedVectors, fixedVectors]

private theorem fixedVectors_c₀_eq_common_iff_mp {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (v : Multiplicative (Fin 3 → ZMod 3))
    (heq : fixedVectors ((StatedSp 3 K).subtype (c₀ hs v)) = {0}) :
    ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  intro i hi
  have hu : (Pi.single (Sum.inl i) (1 : K) : Fin 3 ⊕ Fin 3 → K) ∈
      fixedVectors ((StatedSp 3 K).subtype (c₀ hs v)) := by
    rw [mem_fixedVectors_c₀_iff hs v]
    intro j
    by_cases hj : j = i
    · rw [hj, hi]
      simp [blockVec, Pi.single_apply]
    · have h0 : blockVec (Pi.single (Sum.inl i) (1 : K) : Fin 3 ⊕ Fin 3 → K) j = 0 := by
        funext a
        fin_cases a <;> simp [blockVec, Pi.single_apply, hj]
      rw [h0]
      simp
  have hne : (Pi.single (Sum.inl i) (1 : K) : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero (Sum.inl i)
    simpa [Pi.single_eq_same] using h1
  have hmem : (Pi.single (Sum.inl i) (1 : K) : Fin 3 ⊕ Fin 3 → K) ∈
      ({0} : Set (Fin 3 ⊕ Fin 3 → K)) := by
    rw [← heq]
    exact hu
  rw [Set.mem_singleton_iff] at hmem
  exact hne hmem

theorem fixedVectors_c₀_eq_common_iff {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    fixedVectors ((StatedSp 3 K).subtype (c₀ hs v)) =
        commonFixedVectors (StatedSp 3 K).subtype (c₀ hs) ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  rw [commonFixedVectors_c₀_eq hs]
  constructor
  · intro heq
    exact fixedVectors_c₀_eq_common_iff_mp hs v heq
  · intro hv
    ext w
    constructor
    · intro hw
      rw [Set.mem_singleton_iff]
      apply eq_zero_of_forall_blockVec_eq_zero
      intro i
      have hi := (mem_fixedVectors_c₀_iff hs v w).mp hw i
      have h3 : ¬ 3 ∣ (Multiplicative.toAdd v i).val := by
        have hlt := ZMod.val_lt (Multiplicative.toAdd v i)
        have hne : (Multiplicative.toAdd v i).val ≠ 0 :=
          fun h0 => hv i ((ZMod.val_eq_zero _).mp h0)
        have h12 : (Multiplicative.toAdd v i).val = 1 ∨ (Multiplicative.toAdd v i).val = 2 := by
          omega
        rcases h12 with h12 | h12 <;> rw [h12] <;> norm_num
      exact hs.eq_zero_of_mulVec_pow_eq h3 hi
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      simp [fixedVectors]

theorem c₀_normalizer {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    ∀ n ∈ Subgroup.normalizer ((c₀ hs).range : Set (StatedSp 3 K)),
      ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
        n * c₀ hs v * n⁻¹ =
          c₀ hs (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  intro n hn
  exact exists_signedPerm_of_conj_mem_range (StatedSp 3 K).subtype (c₀ hs) (c₀_injective hs)
    (fixedVectors_c₀_eq_common_iff hs) n fun v => by
      have h : n * c₀ hs v * n⁻¹ ∈ (c₀ hs).range :=
        (Subgroup.mem_set_normalizer_iff.mp hn (c₀ hs v)).mp ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp h
      exact ⟨w, hw.symm⟩

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
