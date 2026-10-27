module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6Basic

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def classListE6Casc : List ℕ := [70, 40, 23, 3]

@[expose] def classListE6Targets : List (List ℕ) := [[70], [61, 62], [58, 56, 55]]

@[expose] def classListE6Reps : List (List (Fin Tag.E6.rank → ℤ)) :=
  [[highRoot .E6], oddDerivE6YFrame, oddDerivE6ZFrame]

@[expose] def classListE6Walks : List (List ℕ × List FrameWalkMove × ℕ) :=
  [([70], [], 0),
    ([40], [.word [1, 3, 4, 2, 3, 1]], 0),
    ([70, 40], [.word [1, 3, 2]], 1),
    ([23], [.word [5, 1, 3, 4, 0, 2, 3, 1]], 0),
    ([70, 23], [.word [5, 1, 3, 4, 0]], 1),
    ([40, 23], [.word [1, 3, 4, 5, 0, 2, 0]], 1),
    ([70, 40, 23], [.word [1, 3, 0, 2, 0]], 2),
    ([3], [.word [4, 5, 2, 1, 3, 4, 0, 2, 3, 1]], 0),
    ([70, 3], [.word [4, 5, 2, 1, 3, 4, 0]], 1),
    ([40, 3], [.word [2, 1, 3, 4, 5, 3, 0, 2, 0]], 1),
    ([70, 40, 3], [.word [4, 2, 1, 3, 0, 2, 0]], 2),
    ([23, 3], [.word [0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 0]], 1),
    ([70, 23, 3], [.word [5, 4, 0, 2, 1, 3, 0, 2, 0]], 2),
    ([40, 23, 3], [.word [1, 3, 4, 5, 2, 3, 4, 0, 2, 3, 0, 2, 0]], 2),
    ([70, 40, 23, 3], [.d4 23 40 67 70 3, .word [1, 3, 0, 2, 0]], 2)]

theorem classListE6_check :
    frameWalkCheck .E6 classListE6Casc classListE6Targets classListE6Walks = true := by
  decide +kernel

theorem classListE6Casc_map :
    classListE6Casc.map Tag.E6.rootCertificate.root = cascadeRoots .E6 := by
  apply List.map_injective_iff.2 List.ofFn_injective
  decide +kernel

theorem classListE6Targets_map :
    classListE6Targets.map (List.map Tag.E6.rootCertificate.root) = classListE6Reps := by
  apply List.map_injective_iff.2 (List.map_injective_iff.2 List.ofFn_injective)
  decide +kernel

variable {K : Type} [Field K]

theorem classListE6_walks [CharP K 2] (S : List (Fin Tag.E6.rank → ℤ))
    (hS : S.Sublist (cascadeRoots .E6)) (hne : S ≠ []) :
    ∃ T ∈ classListE6Reps, FrameProdConj .E6 K S T := by
  rw [← classListE6Casc_map] at hS
  obtain ⟨Sp, hSp, rfl⟩ := List.sublist_map_iff.1 hS
  have hne' : Sp ≠ [] := by
    rintro rfl
    exact hne rfl
  have horth : (classListE6Casc.map Tag.E6.rootCertificate.root).Pairwise
      fun σ σ' => iform σ σ' = 0 := by
    rw [classListE6Casc_map]
    exact frameWalkCascade_pairwise (Or.inr (Or.inl rfl))
  obtain ⟨T, hT, hc⟩ :=
    frameWalkCheck_sound (K := K) (Or.inr (Or.inl rfl)) classListE6_check horth hSp hne'
  refine ⟨T.map Tag.E6.rootCertificate.root, ?_, hc⟩
  rw [← classListE6Targets_map]
  exact List.mem_map_of_mem hT

theorem classListE6Reps_mem (T : List (Fin Tag.E6.rank → ℤ)) (hT : T ∈ classListE6Reps) :
    (⟨(T.map fun σ => pinnedX .E6 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup T⟩ :
      adjointGroup .E6 K) ∈ innerRepsE6 K := by
  simp only [classListE6Reps, List.mem_cons, List.not_mem_nil, or_false] at hT
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hT with rfl | rfl | rfl
  · exact Or.inl (Subtype.ext (by simp))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem exists_conj_mem_innerRepsE6 [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : ∃ g : adjointGroup .E6 K, g * t * g⁻¹ ∈ innerRepsE6 K :=
  exists_conj_mem_of_frame_walks (Or.inr (Or.inl rfl)) classListE6_walks classListE6Reps_mem ht2 ht1

theorem classListE6_hrep [Finite K] [CharP K 2] :
    ∀ t : adjointGroup .E6 K, orderOf (MulAut.conj t) = 2 →
      ∃ ψ : MulAut (adjointGroup .E6 K), ∃ s ∈ innerRepsE6 K, ψ s = t :=
  exists_mulAut_eq_of_frame_walks (Or.inr (Or.inl rfl)) classListE6_walks classListE6Reps_mem

theorem innerInvolutionInput_E6 [Finite K] [CharP K 2] :
    InnerInvolutionInput (adjointGroup .E6 K) :=
  innerInvolutionInput_E6_of_classes classListE6_hrep

theorem innerInvolutionInput_E6' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    InnerInvolutionInput (adjointGroup .E6 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_E6

end CFSG.SeitzReduction
