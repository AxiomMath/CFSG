module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false

section Perfect

variable {τ : Tag}

open CFSG.LieType.Chevalley.SimplyLacedCover CFSG.LieType.Steinberg.Adjoint Matrix in
theorem exists_odd_witness_of_simplyLaced {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (hτ : ∀ i, τ.symmetrizer i i = 1)
    (i : KernelComponent χ) (hi : 2 < (componentRoots χ i).ncard) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) :
    ∃ β ∈ componentRoots χ i, ∃ n : ℤ, Odd n ∧
      n * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ β)) = 2 * (β ⬝ᵥ (τ.symmetrizedCartan *ᵥ α)) := by
  obtain ⟨hαk, hαi⟩ := hα
  by_cases hex : ∃ γ ∈ kernelRoots χ, γ ≠ α ∧ γ ≠ -α ∧ iform α γ ≠ 0
  · obtain ⟨γ, hγk, h1, h2, h3⟩ := hex
    have hγi : γ ∈ componentRoots χ i := by
      refine ⟨hγk, ?_⟩
      rw [← hαi]
      refine Quotient.sound (Relation.EqvGen.rel _ _ ?_)
      show (γ : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (α : Fin τ.rank → ℤ)) ≠ 0
      rw [dotProduct_mulVec_eq_iform, iform_comm]
      exact h3
    have hγr : IsRoot τ γ := hγk.1
    have hαr : IsRoot τ α := hαk.1
    have hm := iform_mem hτ hγr hαr h1 h2
    have hne0 : iform γ α ≠ 0 := by rwa [iform_comm]
    refine ⟨γ, hγi, iform γ α, ?_, ?_⟩
    · rcases hm with h | h | h
      · rw [h]; exact ⟨-1, by norm_num⟩
      · exact absurd h hne0
      · rw [h]; exact ⟨0, by norm_num⟩
    · rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, iform_self_eq_two hτ hγr]
      ring
  · exfalso
    push Not at hex
    have hiso : ∀ γ ∈ kernelRoots χ, γ = α ∨ γ = -α ∨ iform α γ = 0 := by
      intro γ hγ
      by_cases h1 : γ = α
      · exact Or.inl h1
      by_cases h2 : γ = -α
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (hex γ hγ h1 h2))
    have hsub : componentRoots χ i ⊆ {α, -α} := by
      intro γ hγ
      obtain ⟨hγk, hγi⟩ := hγ
      exact eq_or_eq_neg_of_isolated hαk hiso hγk (hγi.trans hαi.symm)
    have hle : (componentRoots χ i).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le α {-α}).trans (by simp))
    omega

theorem isPerfect_componentRootSpan_of_odd {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {M : Type*}
    [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hτ : ∀ i, τ.symmetrizer i i = 1) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) : Group.IsPerfect (componentRootSpan K χ i) := by
  refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le_self _) ?_)
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨β, hβ, n, hn, hodd⟩ := exists_odd_witness_of_simplyLaced hτ i hi hα
  exact pinnedX_mem_commutator_of_odd h2 hα hβ hn hodd c

end Perfect

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem commute_rootSpan_of_commute_component_three_T (hτ : τ ≠ .G2)
    (hsl : ∀ j, τ.symmetrizer j j = 1) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hq : S.D.q = 3) (hrk : 2 < (componentRoots (rootCharHom a) i).ncard)
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  rw [hs1] at hs0 hs hmin hinner
  have : NeZero 1 := ⟨one_ne_zero⟩
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have h3 : (3 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have h22 : (2 : L) * 2 = 1 := by
    have : (2 : L) * 2 = 3 + 1 := by norm_num
    rw [this, h3, zero_add]
  have h2K : (2 : fixSubfield σ) ≠ 0 := by
    intro h
    have h' : (2 : L) = 0 := by
      have e : ((2 : fixSubfield σ) : L) = 2 := map_ofNat (fixSubfield σ).subtype 2
      rw [← e, h]
      rfl
    rw [h', mul_zero] at h22
    exact zero_ne_one h22
  have hperfC := isPerfect_componentRootSpan_of_odd (K := fixSubfield σ) h2K hsl i hrk
  refine commute_rootSpan_of_single_three S hτ i zu hq (hnorm i) ?_ z hcomm
  intro γ hγ t ht
  have hc : σ t = t := by rw [hσ, hq, pow_one]; exact ht
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  have hγ' : γ ∈ unionRoots (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRoots_singleton]
    exact hγ
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  obtain ⟨xt, hxt, hxι⟩ : ∃ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      baseChangeGL (fixSubfield σ).subtype x = pinnedX τ L γ t := by
    have := pinnedX_mem_CQ hγ' hc
    rw [CQ_eq_map] at this
    exact this
  have hy : zu * pinnedX τ L γ t * zu⁻¹ ∈ P.S 0 := by
    rw [hP0]
    exact (hnorm i _).1 (pinnedX_mem_rootSpan hγ _)
  have hrt := norm_mem_rationalComponentT S hT i hs hmin σ zu hnorm hz hperfC ⟨xt, hxt⟩
    ⟨_, hy⟩ (by
      show zu * pinnedX τ L γ t * zu⁻¹ = zu * _ * zu⁻¹
      rw [hxι])
  have hnormeq := norm_eq_list_prod P ⟨_, hy⟩
  have hone : (P.norm ⟨_, hy⟩ : ModGL τ L) = zu * pinnedX τ L γ t * zu⁻¹ := by
    have hd : ∀ k : ZMod 1, k.val = 0 := fun k => by
      rw [Subsingleton.elim k 0, ZMod.val_zero]
    rw [hnormeq]
    simp [Finset.univ_unique, hd, iterHom_zero]
  rw [hone] at hrt
  exact hrt

end Assembly

end CFSG.HardMathSupport.Timmesfeld.LangTorus
