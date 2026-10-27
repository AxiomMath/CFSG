module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Kernel

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint Matrix

theorem inter_componentRoots_of_parent
    {τ : Tag} {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {r : ℕ} (v : Fin r → Fin τ.rank → ℤ)
    (hS : simpleUnion χ = Set.range v) (par : Fin r → Fin r) (k₀ : Fin r)
    (hpar : ∀ k, par k = k ∨ iform (v k) (v (par k)) ≠ 0) (n : ℕ) (hn : ∀ k, par^[n] k = k₀)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨ simpleUnion χ ∩ componentRoots χ i = Set.range v := by
  have hv : ∀ k, v k ∈ kernelRoots χ := fun k => simpleUnion_subset χ (hS ▸ ⟨k, rfl⟩)
  have hcls : ∀ k, (⟦⟨v k, hv k⟩⟧ : KernelComponent χ) = ⟦⟨v k₀, hv k₀⟩⟧ := fun k =>
    (mk_eq_of_parent v hv par hpar n k).trans
      (congrArg _ (Subtype.ext (congrArg v (hn k))))
  by_cases hc : (⟦⟨v k₀, hv k₀⟩⟧ : KernelComponent χ) = i
  · refine Or.inr (Set.ext fun β => ⟨fun h => hS ▸ h.1, fun hβ => ⟨hS ▸ hβ, ?_⟩⟩)
    obtain ⟨k, rfl⟩ := hβ
    exact ⟨hv k, (hcls k).trans hc⟩
  · refine Or.inl (Set.eq_empty_of_forall_notMem fun β ⟨hβS, hβi⟩ => ?_)
    rw [hS] at hβS
    obtain ⟨k, rfl⟩ := hβS
    obtain ⟨h, hi⟩ := hβi
    exact hc ((hcls k).symm.trans hi)

theorem e7_simple_inter_zero
    {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E7 0)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7SimpleRoot := by
  subst hχ
  exact inter_componentRoots_of_parent e7SimpleRoot simpleUnion_e7_zero ![0, 3, 0, 2, 3, 4, 5] 0
    (by decide) 6 (by decide) i

theorem e7_simple_inter_two
    {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E7 2)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7A7Root := by
  subst hχ
  exact inter_componentRoots_of_parent e7A7Root simpleUnion_e7_two ![0, 0, 1, 2, 3, 4, 5] 0
    (by decide) 6 (by decide) i

theorem e7_simple_inter_three
    {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E7 3)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7E6Root := by
  subst hχ
  exact inter_componentRoots_of_parent e7E6Root simpleUnion_e7_three ![0, 3, 0, 2, 3, 4] 0
    (by decide) 5 (by decide) i

theorem e7_one_theta_facts :
    ∀ k, k < e7Certificate.roots.length → inKernel e7Certificate 1 k = true →
      (e7Certificate.root k (e7Node 0) ≠ 0 ∨ iform e7Theta (e7Certificate.root k) ≠ 0) →
        e7Certificate.root k = e7Theta ∨ e7Certificate.root k = -e7Theta := by
  decide +kernel

theorem e7_simple_inter_one
    {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ} (hχ : χ = signMaskChar .E7 1)
    (i : KernelComponent χ) :
    simpleUnion χ ∩ componentRoots χ i = ∅ ∨
      simpleUnion χ ∩ componentRoots χ i = Set.range e7D6Root ∨
      simpleUnion χ ∩ componentRoots χ i = {e7Theta} := by
  subst hχ
  have hS := simpleUnion_e7_one
  have hv : ∀ k, e7D6Root k ∈ kernelRoots (signMaskChar .E7 1) := fun k =>
    simpleUnion_subset (signMaskChar .E7 1) (hS ▸ Or.inl ⟨k, rfl⟩)
  have hθ : e7Theta ∈ kernelRoots (signMaskChar .E7 1) :=
    simpleUnion_subset (signMaskChar .E7 1) (hS ▸ Or.inr rfl)
  have hn : ∀ k : Fin 6, (![0, 0, 1, 2, 3, 3] : Fin 6 → Fin 6)^[5] k = 0 := by decide
  have hcls : ∀ k, (⟦⟨e7D6Root k, hv k⟩⟧ : KernelComponent (signMaskChar .E7 1)) =
      ⟦⟨e7D6Root 0, hv 0⟩⟧ := fun k =>
    (mk_eq_of_parent e7D6Root hv ![0, 0, 1, 2, 3, 3] (by decide) 5 k).trans
      (congrArg _ (Subtype.ext (congrArg e7D6Root (hn k))))
  have hpm : ∀ α ∈ kernelRoots (signMaskChar .E7 1), (α (e7Node 0) ≠ 0 ∨ iform e7Theta α ≠ 0) →
      α = e7Theta ∨ α = -e7Theta := by
    intro α hα h
    obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff e7Certificate_check).1 hα
    exact e7_one_theta_facts k hk hker h
  have hne : (⟦⟨e7Theta, hθ⟩⟧ : KernelComponent (signMaskChar .E7 1)) ≠ ⟦⟨e7D6Root 0, hv 0⟩⟧ := by
    refine mk_ne_of_invariant (fun α => α (e7Node 0) ≠ 0) (fun α β hαβ hα => ?_)
      (show e7Theta (e7Node 0) ≠ 0 by decide) (show ¬ e7D6Root 0 (e7Node 0) ≠ 0 by decide)
    rcases hpm α α.2 (Or.inl hα) with h | h
    · rcases hpm β β.2 (Or.inr (by rwa [← h])) with h' | h' <;> rw [h'] <;> decide
    · rcases hpm β β.2 (Or.inr (by
        rw [h, show -e7Theta = (-1 : ℤ) • e7Theta by simp, iform_smul_left] at hαβ
        intro h0
        exact hαβ (by rw [h0, mul_zero]))) with h' | h' <;> rw [h'] <;> decide
  by_cases h₁ : (⟦⟨e7D6Root 0, hv 0⟩⟧ : KernelComponent (signMaskChar .E7 1)) = i
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
  · by_cases h₂ : (⟦⟨e7Theta, hθ⟩⟧ : KernelComponent (signMaskChar .E7 1)) = i
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

end CFSG.ComponentClassification.CatLeafProof
