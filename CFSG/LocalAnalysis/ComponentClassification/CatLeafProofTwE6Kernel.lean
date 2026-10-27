module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LieType.Chevalley.RationalToralSignDiagramE6

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint Matrix

@[expose] def e6Decomp0 : List (ℕ × ℕ × ℕ) :=
  [(7, 0, 2), (9, 1, 3), (11, 2, 3), (13, 3, 4), (15, 4, 5), (18, 0, 11), (20, 1, 11),
    (21, 1, 13), (23, 2, 13), (25, 3, 15), (28, 0, 20), (29, 0, 23), (32, 1, 23), (33, 1, 25),
    (35, 2, 25), (39, 0, 32), (40, 0, 35), (43, 3, 32), (44, 1, 35), (48, 0, 43), (49, 0, 44),
    (52, 3, 44), (55, 2, 48), (56, 0, 52), (58, 4, 52), (61, 2, 56), (62, 0, 58), (66, 2, 62),
    (68, 3, 66), (70, 1, 68)]

@[expose] def e6Decomp20 : List (ℕ × ℕ × ℕ) :=
  [(9, 1, 3), (29, 0, 23), (32, 1, 23), (35, 5, 23), (39, 0, 32), (40, 0, 35), (43, 3, 32),
    (44, 1, 35), (48, 0, 43), (49, 0, 44), (52, 3, 44), (56, 0, 52), (66, 23, 49), (68, 3, 66),
    (70, 1, 68)]

@[expose] def e6Decomp2 : List (ℕ × ℕ × ℕ) :=
  [(7, 0, 2), (11, 2, 3), (13, 3, 4), (15, 4, 5), (18, 0, 11), (23, 2, 13), (25, 3, 15),
    (29, 0, 23), (35, 2, 25), (40, 0, 35)]

theorem e6_decomp0 : decompCheck e6Certificate e6Splus0 e6Delta0 e6Decomp0 = true := by
  decide +kernel

theorem e6_decomp20 : decompCheck e6Certificate e6Splus20 e6Delta20 e6Decomp20 = true := by
  decide +kernel

theorem e6_decomp2 : decompCheck e6Certificate e6Splus2 e6Delta2 e6Decomp2 = true := by
  decide +kernel

@[expose] def e6SimpleRoot (k : Fin 6) : Fin (Tag.rank .E6) → ℤ := Pi.single (e6Node k) 1

@[expose] def e6D5TwRoot : Fin 5 → Fin (Tag.rank .E6) → ℤ :=
  ![Pi.single (e6Node 3) 1, Pi.single (e6Node 1) 1, ![0, 0, 1, 1, 1, 0], Pi.single (e6Node 0) 1,
    Pi.single (e6Node 5) 1]

@[expose] def e6A5Root (k : Fin 5) : Fin (Tag.rank .E6) → ℤ := Pi.single (e6A5Node k) 1

theorem simpleUnion_e6_zero :
    simpleUnion (signMaskChar .E6 0) = Set.range e6SimpleRoot := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e6Certificate_check e6_splus0 e6_delta0 e6_decomp0]
  have h1 : ∀ d ∈ e6Delta0, ∃ k, e6SimpleRoot k = e6Certificate.root d := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e6Delta0, e6Certificate.root d = e6SimpleRoot k := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨k, rfl⟩
    exact h2 k

theorem simpleUnion_e6_twenty :
    simpleUnion (signMaskChar .E6 20) = Set.range e6D5TwRoot := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e6Certificate_check e6_splus20 e6_delta20 e6_decomp20]
  have h1 : ∀ d ∈ e6Delta20, ∃ k, e6D5TwRoot k = e6Certificate.root d := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e6Delta20, e6Certificate.root d = e6D5TwRoot k := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact h1 d hd
  · rintro ⟨k, rfl⟩
    exact h2 k

theorem simpleUnion_e6_two :
    simpleUnion (signMaskChar .E6 2) = Set.range e6A5Root ∪ {hiE6} := by
  ext β
  rw [mem_simpleUnion_iff_of_decompCheck e6Certificate_check e6_splus2 e6_delta2 e6_decomp2]
  have h1 : ∀ d ∈ e6Delta2, (∃ k, e6A5Root k = e6Certificate.root d) ∨
      e6Certificate.root d = hiE6 := by decide +kernel
  have h2 : ∀ k, ∃ d ∈ e6Delta2, e6Certificate.root d = e6A5Root k := by decide +kernel
  have h3 : ∃ d ∈ e6Delta2, e6Certificate.root d = hiE6 := by decide +kernel
  constructor
  · rintro ⟨d, hd, rfl⟩
    rcases h1 d hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨k, rfl⟩ | h)
    · exact h2 k
    · rw [Set.mem_singleton_iff] at h
      exact h ▸ h3

theorem e6_simple_inter_zero
    {χ : Multiplicative (Fin (Tag.rank .E6) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E6 0)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e6SimpleRoot := by
  subst hχ
  exact inter_componentRoots_of_parent e6SimpleRoot simpleUnion_e6_zero ![2, 3, 3, 3, 3, 4] 3
    (by decide) 3 (by decide) i

theorem e6_simple_inter_twenty
    {χ : Multiplicative (Fin (Tag.rank .E6) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E6 20)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e6D5TwRoot := by
  subst hχ
  exact inter_componentRoots_of_parent e6D5TwRoot simpleUnion_e6_twenty ![1, 2, 2, 2, 2] 2
    (by decide) 2 (by decide) i

theorem e6_two_theta_facts :
    ∀ k, k < e6Certificate.roots.length → inKernel e6Certificate 2 k = true →
      (e6Certificate.root k (e6Node 1) ≠ 0 ∨ iform hiE6 (e6Certificate.root k) ≠ 0) →
        e6Certificate.root k = hiE6 ∨ e6Certificate.root k = -hiE6 := by
  decide +kernel

theorem e6_two_eq_hiE6 {α : Fin (Tag.rank .E6) → ℤ}
    (hα : α ∈ kernelRoots (signMaskChar .E6 2))
    (h : α (e6Node 1) ≠ 0 ∨ iform hiE6 α ≠ 0) : α = hiE6 ∨ α = -hiE6 := by
  obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff e6Certificate_check).1 hα
  exact e6_two_theta_facts k hk hker h

theorem e6_two_invariant
    (α β : kernelRoots (signMaskChar .E6 2)) (hαβ : iform (α : Fin (Tag.rank .E6) → ℤ) β ≠ 0)
    (hα : (α : Fin (Tag.rank .E6) → ℤ) (e6Node 1) ≠ 0) :
    (β : Fin (Tag.rank .E6) → ℤ) (e6Node 1) ≠ 0 := by
  rcases e6_two_eq_hiE6 α.2 (Or.inl hα) with h | h
  · rcases e6_two_eq_hiE6 β.2 (Or.inr (by rwa [← h])) with h' | h' <;> rw [h'] <;> decide
  · rcases e6_two_eq_hiE6 β.2 (Or.inr (by
      rw [h, show -hiE6 = (-1 : ℤ) • hiE6 by simp, iform_smul_left] at hαβ
      intro h0
      exact hαβ (by rw [h0, mul_zero]))) with h' | h' <;> rw [h'] <;> decide

theorem e6_simple_inter_two
    {χ : Multiplicative (Fin (Tag.rank .E6) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E6 2)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e6A5Root ∨
      simpleUnion χ ∩ componentRoots χ i = {hiE6} := by
  subst hχ
  have hS := simpleUnion_e6_two
  have hv : ∀ k, e6A5Root k ∈ kernelRoots (signMaskChar .E6 2) := fun k =>
    simpleUnion_subset (signMaskChar .E6 2) (hS ▸ Or.inl ⟨k, rfl⟩)
  have hθ : hiE6 ∈ kernelRoots (signMaskChar .E6 2) :=
    simpleUnion_subset (signMaskChar .E6 2) (hS ▸ Or.inr rfl)
  have hn : ∀ k : Fin 5, (![0, 0, 1, 2, 3] : Fin 5 → Fin 5)^[4] k = 0 := by decide
  have hcls : ∀ k, (⟦⟨e6A5Root k, hv k⟩⟧ : KernelComponent (signMaskChar .E6 2)) =
      ⟦⟨e6A5Root 0, hv 0⟩⟧ := fun k =>
    (mk_eq_of_parent e6A5Root hv ![0, 0, 1, 2, 3] (by decide) 4 k).trans
      (congrArg _ (Subtype.ext (congrArg e6A5Root (hn k))))
  have hne : (⟦⟨hiE6, hθ⟩⟧ : KernelComponent (signMaskChar .E6 2)) ≠ ⟦⟨e6A5Root 0, hv 0⟩⟧ :=
    mk_ne_of_invariant (fun α => α (e6Node 1) ≠ 0) e6_two_invariant
      (show hiE6 (e6Node 1) ≠ 0 by decide) (show ¬ e6A5Root 0 (e6Node 1) ≠ 0 by decide)
  by_cases h₁ : (⟦⟨e6A5Root 0, hv 0⟩⟧ : KernelComponent (signMaskChar .E6 2)) = i
  · refine Or.inr (Or.inl (Set.ext fun β => ⟨fun ⟨hβS, hβi⟩ => ?_, fun hβ => ?_⟩))
    · rw [hS] at hβS
      rcases hβS with hβ | hβ
      · exact hβ
      · rw [Set.mem_singleton_iff] at hβ
        subst hβ
        obtain ⟨h, hi⟩ := hβi
        exact absurd (hi.trans h₁.symm) hne
    · obtain ⟨k, rfl⟩ := hβ
      exact ⟨hS ▸ Or.inl ⟨k, rfl⟩, hv k, (hcls k).trans h₁⟩
  · by_cases h₂ : (⟦⟨hiE6, hθ⟩⟧ : KernelComponent (signMaskChar .E6 2)) = i
    · refine Or.inr (Or.inr (Set.ext fun β => ⟨fun ⟨hβS, hβi⟩ => ?_, fun hβ => ?_⟩))
      · rw [hS] at hβS
        rcases hβS with ⟨k, rfl⟩ | hβ
        · obtain ⟨h, hi⟩ := hβi
          exact absurd ((hcls k).symm.trans hi) h₁
        · exact hβ
      · rw [Set.mem_singleton_iff] at hβ
        subst hβ
        exact ⟨hS ▸ Or.inr rfl, hθ, h₂⟩
    · refine Or.inl (Set.eq_empty_of_forall_notMem fun β ⟨hβS, hβi⟩ => ?_)
      rw [hS] at hβS
      obtain ⟨h, hi⟩ := hβi
      rcases hβS with ⟨k, rfl⟩ | hβ
      · exact h₁ ((hcls k).symm.trans hi)
      · rw [Set.mem_singleton_iff] at hβ
        subst hβ
        exact h₂ hi

theorem e6Perm_symm_symm (j : Fin (Tag.rank .E6)) :
    TwistTag.E6.perm.symm (TwistTag.E6.perm.symm j) = j := by
  have h : ∀ i : Fin 6, (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) = i := by decide
  exact h j

theorem e6Perm_symm_one : TwistTag.E6.perm.symm (e6Node 1) = e6Node 1 := by
  have h : (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm 1 = 1 := by decide
  exact h

theorem thetaMap_e6_nil_apply
    (γ : Fin (Tag.rank .E6) → ℤ) :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ =
      permLattice (τ := .E6) TwistTag.E6.perm γ := by
  unfold thetaMap
  rw [wordElt_nil, one_smul]

theorem thetaMap_e6_twice
    (γ : Fin (Tag.rank .E6) → ℤ) :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm
      (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) = γ := by
  rw [thetaMap_e6_nil_apply, thetaMap_e6_nil_apply]
  funext j
  change γ (TwistTag.E6.perm.symm (TwistTag.E6.perm.symm j)) = γ j
  rw [e6Perm_symm_symm]

theorem thetaMap_e6_alpha1 :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm (Pi.single (e6Node 0) 1) =
      Pi.single (e6Node 5) 1 := by
  rw [thetaMap_e6_nil_apply]
  funext j
  change (Pi.single (e6Node 0) 1 : Fin (Tag.rank .E6) → ℤ) (TwistTag.E6.perm.symm j) =
    (Pi.single (e6Node 5) 1 : Fin (Tag.rank .E6) → ℤ) j
  have h : ∀ i : Fin 6, (Pi.single 0 1 : Fin 6 → ℤ)
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) = (Pi.single 5 1 : Fin 6 → ℤ) i := by
    decide
  exact h j

theorem thetaMap_e6_hiE6 :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm hiE6 = hiE6 := by
  rw [thetaMap_e6_nil_apply]
  funext j
  change hiE6 (TwistTag.E6.perm.symm j) = hiE6 j
  have h : ∀ i : Fin 6, (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) =
        (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) i := by
    decide
  exact h j

theorem thetaMap_e6_node1
    (γ : Fin (Tag.rank .E6) → ℤ) :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ (e6Node 1) = γ (e6Node 1) := by
  rw [thetaMap_e6_nil_apply]
  exact congrArg γ e6Perm_symm_one

end CFSG.ComponentClassification.CatLeafProof
