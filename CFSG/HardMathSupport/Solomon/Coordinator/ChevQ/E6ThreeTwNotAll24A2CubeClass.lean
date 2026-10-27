module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

set_option linter.unusedSectionVars false

section Classes


theorem ncard_componentRoots_mem {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    (componentRoots (rootCharHom a) i).ncard = 2 ∨ (componentRoots (rootCharHom a) i).ncard = 6 ∨
      (componentRoots (rootCharHom a) i).ncard = 20 ∨
      (componentRoots (rootCharHom a) i).ncard = 24 ∨
      (componentRoots (rootCharHom a) i).ncard = 30 ∨
      (componentRoots (rootCharHom a) i).ncard = 40 ∨
      (componentRoots (rootCharHom a) i).ncard = 72 := by
  obtain ⟨s, hs, h | h⟩ := Up34Exc.RD.size_of_check2 Up34Exc.RD.noG2_E6 73 Up34Exc.RD.okE6
    Up34Exc.RD.rdCheck2_E6 a ha i
  · obtain ⟨h1, h2⟩ := h
    simp only [Up34Exc.RD.okE6, Bool.or_eq_true, beq_iff_eq] at hs
    omega
  · obtain ⟨rfl, -⟩ := h
    simp [Up34Exc.RD.okE6] at hs

theorem finite_kernelRoots_E6 {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M) : (kernelRoots χ).Finite :=
  (finite_setOf_isRoot Tag.E6).subset fun α hα => hα.1

theorem componentRoots_subset_kernelRoots {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M) (i : KernelComponent χ) :
    componentRoots χ i ⊆ kernelRoots χ := fun _ hα => hα.1

theorem disjoint_componentRoots {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {i j : KernelComponent χ} (hij : i ≠ j) :
    Disjoint (componentRoots χ i) (componentRoots χ j) := by
  rw [Set.disjoint_left]
  rintro α ⟨h, hi⟩ ⟨h', hj⟩
  exact hij (hi.symm.trans hj)

theorem mem_componentRoots_class {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots χ) : α ∈ componentRoots χ (⟦⟨α, hα⟩⟧ : KernelComponent χ) :=
  ⟨hα, rfl⟩

theorem kernel_classes_of_ncard_eighteen {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) :
    ∃ c : Fin 3 → KernelComponent (rootCharHom a), Function.Bijective c ∧
      ∀ k, (componentRoots (rootCharHom a) (c k)).ncard = 6 := by
  classical
  have F := kac_facts h3 ha
  by_cases h3c : ∃ i j k : KernelComponent (rootCharHom a), i ≠ j ∧ i ≠ k ∧ j ≠ k
  · obtain ⟨i, j, k, hij, hik, hjk⟩ := h3c
    obtain ⟨hi, hj, hk⟩ := F.three i j k hij hik hjk
    refine ⟨![i, j, k], ⟨?_, ?_⟩, ?_⟩
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]
    · intro l
      by_contra hl
      push Not at hl
      have h0 : i ≠ l := by simpa using hl 0
      have h1 : j ≠ l := by simpa using hl 1
      have h2 : k ≠ l := by simpa using hl 2
      exact F.four i j k l hij hik h0 hjk h1 h2
    · intro x
      fin_cases x <;> simp [hi, hj, hk]
  · exfalso
    push Not at h3c
    have hfin := finite_kernelRoots_E6 (rootCharHom a)
    obtain ⟨α₀, hα₀⟩ : (kernelRoots (rootCharHom a)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    set i₀ : KernelComponent (rootCharHom a) := ⟦⟨α₀, hα₀⟩⟧ with hi₀
    by_cases hall : ∀ k : KernelComponent (rootCharHom a), k = i₀
    · have hsub : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i₀ :=
        fun α hα => ⟨hα, hall _⟩
      have heq : kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i₀ :=
        Set.Subset.antisymm hsub (componentRoots_subset_kernelRoots _ _)
      have := ncard_componentRoots_mem ha i₀
      rw [← heq, h18] at this
      omega
    · push Not at hall
      obtain ⟨j₀, hj₀⟩ := hall
      have hcl : ∀ k : KernelComponent (rootCharHom a), k = i₀ ∨ k = j₀ := by
        intro k
        by_contra hk
        push Not at hk
        exact hk.2 (h3c i₀ j₀ k (Ne.symm hj₀) (Ne.symm hk.1)).symm
      have hsub : kernelRoots (rootCharHom a) ⊆
          componentRoots (rootCharHom a) i₀ ∪ componentRoots (rootCharHom a) j₀ := by
        intro α hα
        rcases hcl ⟦⟨α, hα⟩⟧ with h | h
        · exact Or.inl ⟨hα, h⟩
        · exact Or.inr ⟨hα, h⟩
      have heq : kernelRoots (rootCharHom a) =
          componentRoots (rootCharHom a) i₀ ∪ componentRoots (rootCharHom a) j₀ :=
        Set.Subset.antisymm hsub (Set.union_subset (componentRoots_subset_kernelRoots _ _)
          (componentRoots_subset_kernelRoots _ _))
      have hf₁ : (componentRoots (rootCharHom a) i₀).Finite :=
        hfin.subset (componentRoots_subset_kernelRoots _ _)
      have hf₂ : (componentRoots (rootCharHom a) j₀).Finite :=
        hfin.subset (componentRoots_subset_kernelRoots _ _)
      have hcard := Set.ncard_union_eq (disjoint_componentRoots (Ne.symm hj₀)) hf₁ hf₂
      rw [← heq, h18] at hcard
      have h₁ := ncard_componentRoots_mem ha i₀
      have h₂ := ncard_componentRoots_mem ha j₀
      omega

theorem perm_fin_three_cycle : ∀ g : Equiv.Perm (Fin 3), (∀ x, g x ≠ x) →
    ∀ x, g (g x) ≠ x ∧ (g ^ 3) x = x ∧ ∀ y, ∃ n < 3, (g ^ n) x = y := by
  decide +kernel

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

theorem orbit_dichotomy {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) {c : Fin 3 → KernelComponent (rootCharHom a)}
    (hc : Function.Bijective c) :
    (∃ i, componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) ∨
      ∀ i, componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 ∧
        rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) := by
  classical
  have himg : ∀ k : Fin 3, ∃ m : Fin 3,
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) (c k) =
        componentRoots (rootCharHom a) (c m) := by
    intro k
    obtain ⟨j, hj⟩ := outer_exists_image_component S hT (c k)
    obtain ⟨m, rfl⟩ := hc.2 j
    exact ⟨m, hj⟩
  choose t ht using himg
  have htinj : Function.Injective t := by
    intro k k' h
    have hk : componentRoots (rootCharHom a) (c k) = componentRoots (rootCharHom a) (c k') := by
      apply Set.image_injective.2 S.ρ.injective
      rw [ht k, ht k', h]
    exact hc.1 (eq_of_componentRoots_eq hk)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective t (Finite.injective_iff_bijective.1 htinj)
  have hτ : ∀ k, τ k = t k := fun k => rfl
  have hiter : ∀ (n : ℕ) (k : Fin 3), (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] ''
      componentRoots (rootCharHom a) (c k) = componentRoots (rootCharHom a) (c ((τ ^ n) k)) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [Function.iterate_succ', Set.image_comp, ih k, ht, pow_succ', Equiv.Perm.mul_apply]
      rfl
  by_cases hfix : ∃ k, τ k = k
  · left
    obtain ⟨k, hk⟩ := hfix
    refine ⟨c k, ?_⟩
    have h1 : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) (c k) =
        componentRoots (rootCharHom a) (c k) := by
      rw [hiter 1 k, pow_one, hk]
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT (c k)
    exact le_antisymm (Nat.sInf_le ⟨one_pos, h1⟩) hs0
  · right
    push Not at hfix
    intro i
    obtain ⟨k, rfl⟩ := hc.2 i
    obtain ⟨hcyc2, hcyc3, hcyct⟩ := perm_fin_three_cycle τ hfix k
    obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT (c k)
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) (c k)) with hsdef
    have hsτ : (τ ^ s) k = k := by
      have := hiter s k
      rw [hs] at this
      exact hc.1 (eq_of_componentRoots_eq this.symm)
    have hs3 : s = 3 := by
      by_contra hne
      have hs_ge : s = 1 ∨ s = 2 ∨ 4 ≤ s := by omega
      rcases hs_ge with h | h | h
      · rw [h, pow_one] at hsτ
        exact hfix k hsτ
      · rw [h, pow_two, Equiv.Perm.mul_apply] at hsτ
        exact hcyc2 hsτ
      · apply hmin 3 (by norm_num) (by omega)
        rw [hiter 3 k, hcyc3]
    refine ⟨hs3, ?_⟩
    ext γ
    constructor
    · rintro ⟨n, δ, hδ, rfl⟩
      have hmem : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] δ ∈
          (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] '' componentRoots (rootCharHom a) (c k) :=
        ⟨δ, hδ, rfl⟩
      rw [hiter n k] at hmem
      exact componentRoots_subset_kernelRoots _ _ hmem
    · intro hγ
      obtain ⟨m, hm⟩ := hc.2 (⟦⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a))
      obtain ⟨n, -, hn⟩ := hcyct m
      have hγm : γ ∈ componentRoots (rootCharHom a) (c m) := by
        rw [hm]
        exact mem_componentRoots_class hγ
      rw [← hn, ← hiter n k] at hγm
      obtain ⟨δ, hδ, hδγ⟩ := hγm
      exact ⟨n, δ, hδ, hδγ.symm⟩

end Classes

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
