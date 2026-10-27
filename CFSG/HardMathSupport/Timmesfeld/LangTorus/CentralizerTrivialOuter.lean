module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterPass

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Any

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem commute_rootSpan_of_commute_component_of_field_or_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (z : ModGL τ L)
    (hCase : 3 ≤ S.D.q ∨
      (S.D.step z = z ∧
        (∀ j : KernelComponent (rootCharHom a), z ∈ Subgroup.normalizer
          (rootSpan τ L (componentRoots (rootCharHom a) j) : Set _)) ∧
        3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨f, z₀, φ₁, hf, hwpos, hpin, hz₀n, hφ₁, hφ₁S, -⟩ := outer_exists_lang_data S hT i
  have hQ4m : ∀ m, 0 < m →
      4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m) :=
    fun m hm => hQ4.trans (Nat.pow_le_pow_right S.q_pos (Nat.le_mul_of_pos_right _ hm))
  have hz₀' : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun g hg =>
    (hz₀n g).1 hg
  have hfirst : ∀ δ ∈ componentRoots (rootCharHom a) i, ∀ m, 0 < m → f^[m] δ = δ →
      (∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0) →
      ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹) :=
    fun δ hδ m hm hper horth => outer_commute_first_of_field_or_fixed S hτ hT i hz₀' hφ₁ hφ₁S hf hwpos
      hpin hδ hm (hQ4m m hm) hper horth z hCase hcomm
  have hall : ∀ δ ∈ posRoots (componentRoots (rootCharHom a) i), ∀ B : SL2 L,
      Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹) := by
    intro δ hδ
    rcases outerRoots_dichotomy hΨ hf hwpos hδ with horth | ⟨k, hk, hper, hpair, horth⟩
    · exact hfirst δ hδ.1 _ (outerRoots_minimalPeriod_pos hΨ hf hδ.1)
        Function.iterate_minimalPeriod horth
    · have hb : OuterBlock f δ k :=
        ⟨hk, hper, hpair, fun n hn hn2 hnk => horth n hn (by rw [hper]; exact hn2) hnk⟩
      have hω := outerRoots_block_mem hΨ hwpos hδ hb
      refine outer_commute_second_of_field_or_fixed S hτ hT i hz₀' hφ₁ hφ₁S hf hwpos hpin hδ hb (hQ4m k hk) z
        hCase hcomm ?_
      intro j B
      refine hfirst _ (outerRoots_iterate_mem hf j hω.1) k hk ?_ ?_ B
      · rw [← Function.iterate_add_apply, Nat.add_comm k j, Function.iterate_add_apply,
          outerRoots_block_fixed hΨ hf hwpos hδ hb]
      · intro n hn hnk
        rw [← Function.iterate_add_apply,
          outerRoots_iform_iterate hf hω.1 (Nat.le_add_left j n), Nat.add_sub_cancel]
        exact outerRoots_block_orthogonal hΨ hf hwpos hδ hb hn hnk
  have hgen : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ t : L,
      Commute z (z₀ * pinnedX τ L γ t * z₀⁻¹) := by
    intro γ hγ t
    have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
    rcases mem_posRoots_or_mem_negRoots hΨ hγ with hp | hn
    · have hmem : pinnedX τ L γ t ∈ rootRankOneGroup τ L γ := by
        rw [rootRankOneGroup, range_rootSL2_of_isRoot hγr]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
      obtain ⟨B, hB⟩ := hmem
      rw [← hB]
      exact hall γ hp B
    · have hmem : pinnedX τ L γ t ∈ rootRankOneGroup τ L (-γ) := by
        rw [rootRankOneGroup, range_rootSL2_of_isRoot (IsRoot.neg hγr), neg_neg]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩)
      obtain ⟨B, hB⟩ := hmem
      rw [← hB]
      exact hall (-γ) hn B
  have hmap : (rootSpan τ L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj z₀).toMonoidHom ≤ Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen γ hγ t).symm.eq
  intro g hg
  have hg' : z₀⁻¹ * g * z₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine (hz₀n _).2 ?_
    have : z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj z₀).toMonoidHom (z₀⁻¹ * g * z₀) = g := by
    show z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g
    group
  have hmem : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem)
theorem commute_rootSpan_of_commute_component_anyT (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hq3 : 3 ≤ S.D.q)
    (hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  exact commute_rootSpan_of_commute_component_of_field_or_fixed S hτ hT i hQ4 z
    (Or.inl hq3) hcomm

theorem commute_rootSpan_of_commute_component_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (z : ModGL τ L) (hzF : S.D.step z = z)
    (hzN : ∀ j : KernelComponent (rootCharHom a), z ∈ Subgroup.normalizer
      (rootSpan τ L (componentRoots (rootCharHom a) j) : Set _))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  exact commute_rootSpan_of_commute_component_of_field_or_fixed S hτ hT i hQ4 z
    (Or.inr ⟨hzF, hzN, by omega⟩) hcomm

end Any

end CFSG.HardMathSupport.Timmesfeld.LangTorus
