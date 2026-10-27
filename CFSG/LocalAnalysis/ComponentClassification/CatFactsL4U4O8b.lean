module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Assembly.GL83LieDefs

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8 (chainHom chainHom_val chain_down)

attribute [local instance] GSThmB.Catalog7Std.Om8.finite_linearEquiv

variable {K : Type} [Field K] {b c : K} (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c))
  (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
  (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x)
  (hφ : ∀ x, theta K b c hQ0 (φ x) =
    projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x))

include hφ in
theorem map_fixSub :
    (OutInv.fixSub φ).map (theta K b c hQ0).toMonoidHom =
      fixedSubgroup (projectiveConjugation (Q8 K b c) A μ hsim) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x) = theta K b c hQ0 x
    rw [← hφ, OutInv.mem_fixSub.mp hx]
  · intro hy
    refine ⟨(theta K b c hQ0).symm y, OutInv.mem_fixSub.mpr ?_, by simp⟩
    apply (theta K b c hQ0).injective
    rw [hφ, MulEquiv.apply_symm_apply]
    exact hy

abbrev isoFix : OutInv.fixSub φ ≃* fixedSubgroup (projectiveConjugation (Q8 K b c) A μ hsim) :=
  ((theta K b c hQ0).subgroupMap (OutInv.fixSub φ)).trans
    (MulEquiv.subgroupCongr (map_fixSub hQ0 φ A μ hsim hφ))

theorem isoFix_val (x : OutInv.fixSub φ) :
    (isoFix hQ0 φ A μ hsim hφ x).val = theta K b c hQ0 x.val := rfl

variable [Finite K]

include hφ in
theorem exists_lift (J' : Subgroup (G0 K b c)) (hJφ : J' ≤ OutInv.fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (OutInv.fixSub φ))) :
    ∃ M : Subgroup ((orthogonalDerived (Q8 K b c)).subgroupOf
        (fixedSubgroup (similarityConjugation (Q8 K b c) A μ hsim))),
      IsPComponent 2 M ∧ Nat.card J' ∣ Nat.card M ∧
        ∀ x : G0 K b c, x ∈ J' ↔ ∃ m ∈ M, QuotientGroup.mk'
          ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c)))
          (⟨m.val.val, m.property⟩ : orthogonalDerived (Q8 K b c)) = theta K b c hQ0 x := by
  set e := isoFix hQ0 φ A μ hsim hφ
  set L' := (J'.subgroupOf (OutInv.fixSub φ)).map e.toMonoidHom with hL'def
  have hL' : IsPComponent 2 L' := CatalogueBAlternating.pComponent_map_equiv 2 e _
    (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hJ)
  obtain ⟨M, hM, hML⟩ := chain_down (orthogonalDerived (Q8 K b c)) (scalarSigns (Q8 K b c))
    (similarityConjugation (Q8 K b c) A μ hsim) (orthogonalDerived_invariant (Q8 K b c) A μ hsim)
    (scalarSigns_invariant (Q8 K b c) A μ hsim) (scalarSigns_central (Q8 K b c)) L' hL'
  refine ⟨M, hM, ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : Nat.card J' = Nat.card L' := by
      rw [hL'def, Subgroup.card_map_of_injective e.injective]
      exact (Nat.card_congr (subgroupOfEquivOfLe hJφ).toEquiv).symm
    rw [h1, ← hML]
    exact Subgroup.card_map_dvd M _
  · have hx' : e ⟨x, hJφ hx⟩ ∈ L' := mem_map_of_mem _ (mem_subgroupOf.mpr hx)
    rw [← hML] at hx'
    obtain ⟨m, hm, hme⟩ := hx'
    refine ⟨m, hm, ?_⟩
    rw [← chainHom_val]
    exact congrArg Subtype.val hme
  · rintro ⟨m, hm, hmx⟩
    have hmL : chainHom _ _ _ _ _ m ∈ L' := hML ▸ mem_map_of_mem _ hm
    have hfix : theta K b c hQ0 x ∈ fixedSubgroup (projectiveConjugation (Q8 K b c) A μ hsim) := by
      rw [← hmx, ← chainHom_val]
      exact (chainHom _ _ _ _ _ m).property
    have hxφ : x ∈ OutInv.fixSub φ := by
      rw [← map_fixSub hQ0 φ A μ hsim hφ] at hfix
      obtain ⟨x', hx', hxx'⟩ := hfix
      rwa [← (theta K b c hQ0).injective hxx']
    have heq : e ⟨x, hxφ⟩ = chainHom _ _ _ _ _ m := by
      apply Subtype.ext
      rw [isoFix_val, chainHom_val]
      exact hmx.symm
    rw [← heq] at hmL
    obtain ⟨y, hy, hye⟩ := hmL
    have hyx : y = ⟨x, hxφ⟩ := e.injective hye
    rw [hyx] at hy
    exact mem_subgroupOf.mp hy

omit [Finite K] in
theorem card_dvd_centralizer (M : Subgroup ((orthogonalDerived (Q8 K b c)).subgroupOf
    (fixedSubgroup (similarityConjugation (Q8 K b c) A μ hsim)))) :
    Nat.card M ∣ Nat.card (orthogonalOperatorCentralizer (Q8 K b c) A.toLinearMap) := by
  rw [← Nat.card_congr (fixedCentralizerEquiv (Q8 K b c) A μ hsim).toEquiv]
  exact (Subgroup.card_subgroup_dvd_card M).trans (Subgroup.card_subgroup_dvd_card _)

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
