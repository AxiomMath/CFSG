module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwDatum
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.ToralSign
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Upgrade

section Classes

variable {τ : Tag} {M : Type*} [CommGroup M]

theorem exists_eq_or_neg_of_orthogonal
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (horth : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ β' ∈ simpleRoots (componentRoots χ i),
      β ≠ β' → iform β β' = 0)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) :
    ∃ β ∈ simpleRoots (componentRoots χ i), γ = β ∨ γ = -β := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hself : ∀ β ∈ simpleRoots (componentRoots χ i), iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (simpleRoots_isRoot hβ)
  have hpos : ∀ α ∈ posRoots (componentRoots χ i),
      ∃ β ∈ simpleRoots (componentRoots χ i), α = β := by
    intro α hα
    obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hα
    have hαα : iform α α = 2 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact rootForm_self hτ (hΨ.isRoot α hα.1)
    have hβα : ∀ β ∈ simpleRoots (componentRoots χ i), iform β α = 2 * c β := by
      intro β hβ
      conv_lhs => rw [e]
      rw [iform_finset_sum_right, Finset.sum_eq_single β]
      · rw [iform_smul_right, hself β hβ]
        ring
      · intro β' hβ' hne
        rw [iform_smul_right, horth β hβ β' hβ' (Ne.symm hne), mul_zero]
      · intro h
        exact absurd hβ h
    have hsum : ∑ β ∈ simpleRoots (componentRoots χ i), c β * c β = 1 := by
      have h1 : iform α α = ∑ β ∈ simpleRoots (componentRoots χ i), c β * iform β α := by
        conv_lhs => arg 1; rw [e]
        rw [iform_finset_sum_left]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [iform_smul_left]
      rw [hαα] at h1
      have h2 : ∑ β ∈ simpleRoots (componentRoots χ i), c β * iform β α =
          2 * ∑ β ∈ simpleRoots (componentRoots χ i), c β * c β := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β hβ => ?_
        rw [hβα β hβ]
        ring
      omega
    obtain ⟨β₀, hβ₀, hcβ₀⟩ : ∃ β ∈ simpleRoots (componentRoots χ i), c β ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : α = 0 := by
        rw [e]
        exact Finset.sum_eq_zero fun β hβ => by rw [hcon β hβ, zero_smul]
      exact (hΨ.isRoot α hα.1).ne_zero this
    have hcpos : 1 ≤ c β₀ := by have := hc β₀ hβ₀; omega
    have h1 : c β₀ * c β₀ + ∑ β ∈ (simpleRoots (componentRoots χ i)).erase β₀, c β * c β = 1 := by
      have := Finset.add_sum_erase (simpleRoots (componentRoots χ i)) (fun β => c β * c β) hβ₀
      rw [← hsum]
      exact this
    have h2 : 0 ≤ ∑ β ∈ (simpleRoots (componentRoots χ i)).erase β₀, c β * c β :=
      Finset.sum_nonneg fun β _ => mul_self_nonneg _
    have h5 : 1 ≤ c β₀ * c β₀ := by nlinarith
    have h3 : c β₀ * c β₀ = 1 := by linarith
    have hone : c β₀ = 1 := by nlinarith
    have hothers : ∀ β ∈ simpleRoots (componentRoots χ i), β ≠ β₀ → c β = 0 := by
      have h4 : ∑ β ∈ (simpleRoots (componentRoots χ i)).erase β₀, c β * c β = 0 := by linarith
      intro β hβ hne
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun β _ => mul_self_nonneg (c β))).1 h4 β
        (Finset.mem_erase.2 ⟨hne, hβ⟩)
      nlinarith
    refine ⟨β₀, hβ₀, ?_⟩
    rw [e, Finset.sum_eq_single β₀]
    · rw [hone, one_smul]
    · intro β hβ hne
      rw [hothers β hβ hne, zero_smul]
    · intro h
      exact absurd hβ₀ h
  rcases mem_posRoots_or_mem_negRoots hΨ hγ with h | h
  · obtain ⟨β, hβ, hβe⟩ := hpos γ h
    exact ⟨β, hβ, Or.inl hβe⟩
  · obtain ⟨β, hβ, hβe⟩ := hpos (-γ) h
    exact ⟨β, hβ, Or.inr (neg_eq_iff_eq_neg.mp hβe)⟩


def UniqueIsolated (χ : Multiplicative (Fin τ.rank → ℤ) →* M) : Prop :=
  ∀ β ∈ kernelRoots χ, ∀ β' ∈ kernelRoots χ,
    (∀ γ ∈ kernelRoots χ, iform β γ ≠ 0 → γ = β ∨ γ = -β) →
    (∀ γ ∈ kernelRoots χ, iform β' γ ≠ 0 → γ = β' ∨ γ = -β') → β' = β ∨ β' = -β

theorem isolated_of_orthogonal (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (horth : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ β' ∈ simpleRoots (componentRoots χ i),
      β ≠ β' → iform β β' = 0)
    {β₁ : Fin τ.rank → ℤ} (hβ₁ : β₁ ∈ simpleRoots (componentRoots χ i)) :
    ∀ γ ∈ kernelRoots χ, iform β₁ γ ≠ 0 → γ = β₁ ∨ γ = -β₁ := by
  intro γ hγK hγ
  obtain ⟨hβ₁K, hclass⟩ := simpleRoots_subset hβ₁
  have hsame : (⟦⟨γ, hγK⟩⟧ : KernelComponent χ) = i := by
    rw [← hclass]
    exact mk_eq_of_iform_ne_zero (α := ⟨γ, hγK⟩) (β := ⟨β₁, hβ₁K⟩)
      (by change iform γ β₁ ≠ 0; rw [iform_comm]; exact hγ)
  obtain ⟨β, hβ, hγβ⟩ := exists_eq_or_neg_of_orthogonal hτ i horth (γ := γ) ⟨hγK, hsame⟩
  by_cases hbb : β = β₁
  · subst hbb
    exact hγβ
  · exfalso
    have h0 := horth β₁ hβ₁ β hβ (Ne.symm hbb)
    rcases hγβ with rfl | rfl
    · exact hγ h0
    · exact hγ (by rw [iform_neg_right_eq, h0, neg_zero])

end Classes

section Orbits

open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitCard_eq_one_of_uniqueIsolated (hUI : UniqueIsolated D.χ) {J' : Set.range D.classOrbit}
    {O₀ : Set (Fin τ.rank → ℤ)} (hO₀ : O₀ ∈ (D.withOrbit J').orbits)
    (hA : (D.withOrbit J').orbits = {O₀}) : orbitCard O₀ = 1 := by
  by_contra hne
  set D' := D.withOrbit J' with hD'
  have hd : 2 ≤ orbitCard O₀ := by
    have := D'.orbitCard_pos hO₀
    omega
  set β := D'.orbitVec O₀ 0 with hβ
  set β' := D'.orbitVec O₀ 1 with hβ'
  have hββ' : β ≠ β' := fun h => by
    have := D'.orbitVec_injOn hO₀ (by omega) (by omega) h
    omega
  have hmem : ∀ j, ∃ i ∈ (J' : Set (KernelComponent D.χ)),
      D'.orbitVec O₀ j ∈ simpleRoots (componentRoots D.χ i) := fun j =>
    D'.mem_unionSimpleRoots_of_mem_orbits hO₀ (D'.orbitVec_mem hO₀ j)
  obtain ⟨i, hi, hβi⟩ := hmem 0
  obtain ⟨i', hi', hβ'i'⟩ := hmem 1
  have hiso := isolated_of_orthogonal D.simplyLaced i
    (simpleRoots_orthogonal_of_orbits_eq D hA hi) hβi
  have hiso' := isolated_of_orthogonal D.simplyLaced i'
    (simpleRoots_orthogonal_of_orbits_eq D hA hi') hβ'i'
  have hKβ : β ∈ kernelRoots D.χ := D'.mem_kernelRoots_of_mem_orbits hO₀ (D'.orbitVec_mem hO₀ 0)
  have hKβ' : β' ∈ kernelRoots D.χ := D'.mem_kernelRoots_of_mem_orbits hO₀ (D'.orbitVec_mem hO₀ 1)
  have hheight : ∀ j, 0 < height (D'.orbitVec O₀ j) := fun j =>
    (mem_posRoots_of_mem_unionSimpleRoots (D'.orbitVec_mem_unionSimpleRoots hO₀ j)).2
  rcases hUI β hKβ β' hKβ' hiso hiso' with h | h
  · exact hββ' h.symm
  · have h1 := hheight 1
    have h2 := hheight 0
    have h3 : height β' = -height β := by rw [h, height_neg]
    have h4 : 0 < height β' := h1
    have h5 : 0 < height β := h2
    omega

end Orbits


section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def isolatedAt (m k : ℕ) : Bool :=
  (List.range C.roots.length).all fun k' =>
    !inKernel C m k' || decide (cpair (C.root k) (C.root k') = 0) ||
      decide (C.root k' = C.root k) || decide (C.root k' = -C.root k)

@[expose] def uniqueIsolatedCheck (m : ℕ) : Bool :=
  (List.range C.roots.length).all fun k => !inKernel C m k || !isolatedAt C m k ||
    (List.range C.roots.length).all fun k' =>
      !inKernel C m k' || !isolatedAt C m k' ||
        decide (C.root k' = C.root k) || decide (C.root k' = -C.root k)

variable {C}

theorem uniqueIsolated_of_check (hC : C.check = true) (hS : τ.symmetrizedCartan = τ.cartan)
    {m : ℕ} (h : uniqueIsolatedCheck C m = true) : UniqueIsolated (signMaskChar τ m) := by
  have hiso : ∀ {k : ℕ}, k < C.roots.length → inKernel C m k = true →
      (∀ γ ∈ kernelRoots (signMaskChar τ m), iform (C.root k) γ ≠ 0 →
        γ = C.root k ∨ γ = -C.root k) → isolatedAt C m k = true := by
    intro k hk hker hI
    simp only [isolatedAt, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    intro j hj
    by_cases hjk : inKernel C m j = true
    · have hjK : C.root j ∈ kernelRoots (signMaskChar τ m) :=
        (mem_kernelRoots_iff hC).2 ⟨j, hj, rfl, hjk⟩
      by_cases h0 : cpair (C.root k) (C.root j) = 0
      · exact Or.inl (Or.inl (Or.inr h0))
      · rcases hI _ hjK (by rwa [iform_eq_cpair hS]) with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
    · exact Or.inl (Or.inl (Or.inl (by simpa using hjk)))
  intro β hβ β' hβ' hI hI'
  obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hβ
  obtain ⟨k', hk', rfl, hker'⟩ := (mem_kernelRoots_iff hC).1 hβ'
  have h1 := hiso hk hker hI
  have h2 := hiso hk' hker' hI'
  unfold uniqueIsolatedCheck at h
  have h3 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simp only [hker, h1, Bool.not_true, Bool.false_or] at h3
  have h4 := List.all_eq_true.1 h3 k' (List.mem_range.2 hk')
  simp only [hker', h2, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h4
  exact h4

end Check

theorem e6_symmetrizedCartan : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
  rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]

theorem e6_uniqueIsolatedCheck_zero : uniqueIsolatedCheck e6Certificate 0 = true := by
  decide +kernel

theorem e6_uniqueIsolatedCheck_twenty : uniqueIsolatedCheck e6Certificate 20 = true := by
  decide +kernel

theorem e6_uniqueIsolatedCheck_two : uniqueIsolatedCheck e6Certificate 2 = true := by
  decide +kernel

theorem e6_uniqueIsolated_zero : UniqueIsolated (signMaskChar Tag.E6 0) :=
  uniqueIsolated_of_check e6Certificate_check e6_symmetrizedCartan e6_uniqueIsolatedCheck_zero

theorem e6_uniqueIsolated_twenty : UniqueIsolated (signMaskChar Tag.E6 20) :=
  uniqueIsolated_of_check e6Certificate_check e6_symmetrizedCartan e6_uniqueIsolatedCheck_twenty

theorem e6_uniqueIsolated_two : UniqueIsolated (signMaskChar Tag.E6 2) :=
  uniqueIsolated_of_check e6Certificate_check e6_symmetrizedCartan e6_uniqueIsolatedCheck_two
end CFSG.ClassicalInvolution.Upgrade
