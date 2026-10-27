module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ChainsBasic

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps

theorem f4Frame_roots :
    List.ofFn (orbitCertRoot .F4 47) = [2, 3, 4, 2] ∧
      List.ofFn (orbitCertRoot .F4 44) = [1, 2, 3, 2] ∧
      List.ofFn (orbitCertRoot .F4 32) = [0, 1, 2, 2] ∧
      List.ofFn (orbitCertRoot .F4 30) = [0, 1, 2, 0] ∧
      List.ofFn (orbitCertRoot .F4 27) = [0, 1, 0, 0] ∧
      List.ofFn (orbitCertRoot .F4 35) = [1, 1, 1, 0] ∧
      List.ofFn (orbitCertRoot .F4 40) = [1, 2, 2, 0] ∧
      List.ofFn (orbitCertRoot .F4 33) = [1, 0, 0, 0] ∧
      List.ofFn (orbitCertRoot .F4 25) = [0, 0, 1, 0] ∧
      List.ofFn (orbitCertRoot .F4 41) = [1, 2, 2, 1] ∧
      List.ofFn (orbitCertRoot .F4 45) = [1, 2, 4, 2] := by
  decide +kernel

@[expose] def f4FrameChainB : List F4CollMove :=
  [.weyl [3, 2, 0, 1, 2, 3, 1, 0], .root 25, .weyl [3, 2, 1, 2, 0, 1, 2, 1, 0, 2, 3, 1, 2]]

@[expose] def f4FrameChainC : List F4CollMove :=
  [.weyl [0, 1, 2, 3, 1, 2, 0], .root 24, .weyl [2, 1, 2, 3], .root 28, .root 26,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainD : List F4CollMove :=
  [.root 24, .weyl [2, 1, 2, 3], .root 28, .root 26, .root 38, .root 40, .root 39,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainE : List F4CollMove :=
  [.weyl [0, 1, 2, 3, 1, 2, 0], .root 30, .root 28, .root 26,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainF : List F4CollMove :=
  [.weyl [0, 1, 2, 3, 1, 0], .root 30, .root 28, .root 26, .root 38, .root 40, .root 39,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainG : List F4CollMove :=
  [.weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 2, 3, 1, 2, 1]]

@[expose] def f4FrameChainH : List F4CollMove :=
  [.weyl [2, 1, 2, 0, 1, 2, 3], .root 38, .root 40, .root 39,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainI : List F4CollMove :=
  [.weyl [0, 1, 2, 3, 1, 2, 1], .root 30, .root 28, .root 26,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

@[expose] def f4FrameChainJ : List F4CollMove :=
  [.weyl [0, 1, 2, 3], .root 30, .root 28, .root 26, .root 38, .root 40, .root 39,
    .weyl [2, 1, 2, 3, 1, 2, 0, 1, 2, 0]]

theorem f4FrameChain_check :
    f4CollOK 64 f4FrameChainB [47, 32] [47, 44] = true ∧
      f4CollOK 64 f4FrameChainC [47, 32, 30] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainD [47, 32, 30, 27] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainE [44, 35, 30] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainF [44, 35, 30, 27] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainG [44, 40] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainH [44, 40, 33] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainI [44, 40, 25] [41, 45] = true ∧
      f4CollOK 64 f4FrameChainJ [44, 40, 33, 25] [41, 45] = true := by
  decide +kernel

@[expose] def f4FrameCandidates : List (List ℕ) :=
  [[47], [47, 32], [47, 32, 30], [47, 32, 30, 27], [44, 35, 30], [44, 35, 30, 27], [44, 40],
    [44, 40, 33], [44, 40, 25], [44, 40, 33, 25]]

section Products

variable {K : Type} [Field K]

theorem exists_conj_f4FrameA :
    ∃ g ∈ adjointGroup .F4 K, g * f4x K 47 1 * g⁻¹ = f4x K 47 1 :=
  ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩

theorem f4CollProd_mem (L : List ℕ) : f4CollProd K L ∈ adjointGroup .F4 K := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact pinnedX_mem_adjointGroup _ _

theorem f4CollProd_pair (a b : ℕ) : f4CollProd K [a, b] = f4x K a 1 * f4x K b 1 := by
  simp

end Products


variable {K : Type} [Field K] [CharP K 2]

theorem exists_conj_f4FrameB :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 47 1 * f4x K 32 1) * g⁻¹ = f4x K 47 1 * f4x K 44 1 := by
  simpa [mul_assoc] using exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.1

theorem exists_conj_f4FrameC :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 47 1 * f4x K 32 1 * f4x K 30 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.1

theorem exists_conj_f4FrameD :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 47 1 * f4x K 32 1 * f4x K 30 1 * f4x K 27 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.1

theorem exists_conj_f4FrameE :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 35 1 * f4x K 30 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.1

theorem exists_conj_f4FrameF :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 35 1 * f4x K 30 1 * f4x K 27 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using
    exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.2.1

theorem exists_conj_f4FrameG :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 40 1) * g⁻¹ = f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using
    exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.2.2.1

theorem exists_conj_f4FrameH :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 40 1 * f4x K 33 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using
    exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.2.2.2.1

theorem exists_conj_f4FrameI :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 40 1 * f4x K 25 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using
    exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.2.2.2.2.1

theorem exists_conj_f4FrameJ :
    ∃ g ∈ adjointGroup .F4 K, g * (f4x K 44 1 * f4x K 40 1 * f4x K 33 1 * f4x K 25 1) * g⁻¹ =
      f4x K 41 1 * f4x K 45 1 := by
  simpa [mul_assoc] using
    exists_conj_of_f4CollOK (K := K) 64 _ _ _ f4FrameChain_check.2.2.2.2.2.2.2.2

theorem exists_conj_of_mem_f4FrameCandidates {L : List ℕ} (hL : L ∈ f4FrameCandidates) :
    ∃ g ∈ adjointGroup .F4 K, g * f4CollProd K L * g⁻¹ = f4x K 47 1 ∨
      g * f4CollProd K L * g⁻¹ = f4x K 47 1 * f4x K 44 1 ∨
      g * f4CollProd K L * g⁻¹ = f4x K 41 1 * f4x K 45 1 := by
  simp only [f4FrameCandidates, List.mem_cons, List.not_mem_nil, or_false] at hL
  obtain ⟨hB, hC, hD, hE, hF, hG, hH, hI, hJ⟩ := f4FrameChain_check
  have hv : ∀ {L : List ℕ} {ms : List F4CollMove}, f4CollOK 64 ms L [41, 45] = true →
      ∃ g ∈ adjointGroup .F4 K, g * f4CollProd K L * g⁻¹ = f4x K 47 1 ∨
        g * f4CollProd K L * g⁻¹ = f4x K 47 1 * f4x K 44 1 ∨
        g * f4CollProd K L * g⁻¹ = f4x K 41 1 * f4x K 45 1 := fun h => by
    obtain ⟨g, hg, h⟩ := exists_conj_of_f4CollOK (K := K) 64 _ _ _ h
    exact ⟨g, hg, Or.inr (Or.inr (h.trans (f4CollProd_pair 41 45)))⟩
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, Or.inl (by simp)⟩
  · obtain ⟨g, hg, h⟩ := exists_conj_of_f4CollOK (K := K) 64 _ _ _ hB
    exact ⟨g, hg, Or.inr (Or.inl (h.trans (f4CollProd_pair 47 44)))⟩
  exacts [hv hC, hv hD, hv hE, hv hF, hv hG, hv hH, hv hI, hv hJ]

theorem exists_mulAut_of_mem_f4FrameCandidates {L : List ℕ} (hL : L ∈ f4FrameCandidates) :
    ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩,
        ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩} : Set (adjointGroup .F4 K)),
      ψ s = ⟨f4CollProd K L, f4CollProd_mem L⟩ := by
  obtain ⟨g, hg, h⟩ := exists_conj_of_mem_f4FrameCandidates (K := K) hL
  have key : ∀ y : adjointGroup .F4 K, (g * f4CollProd K L * g⁻¹ = y) →
      MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K)⁻¹ y = ⟨f4CollProd K L, f4CollProd_mem L⟩ := by
    intro y hy
    apply Subtype.ext
    simp only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hy]
    group
  refine ⟨MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K)⁻¹, ?_⟩
  rcases h with h | h | h
  · exact ⟨_, Set.mem_insert _ _, key _ h⟩
  · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert _ _), key _ h⟩
  · exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), key _ h⟩

end CFSG.SeitzReduction
