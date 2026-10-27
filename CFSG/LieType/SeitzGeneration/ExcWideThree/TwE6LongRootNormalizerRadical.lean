module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootNormalizer

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Radical


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem graphFixedParabolicRadical_subgroupOf_le_twE6LongRootRadical :
    (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0).subgroupOf
        (twistedE6RootGroup K σ) ≤
      twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) := by
  haveI : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQn, -, -, -, -, -, -, hpg, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ J0
  let φ : twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) →*
      ModGL TwistTag.E6.tag K :=
    (twistedE6RootGroup K σ).subtype.comp
      (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).subtype
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Subtype.ext h)
  have hmem : ∀ g : twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot),
      φ g ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 := fun g =>
    (mem_twE6LongRootParabolic_iff σ g.1).1 g.2
  have hnormal : ((graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0).comap φ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (⟨φ n, hmem n⟩ : graphFixedParabolic TwistTag.E6 K σ.toRingHom J0) ∈
        (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0).subgroupOf
          (graphFixedParabolic TwistTag.E6 K σ.toRingHom J0) := hn
    exact hQn.conj_mem _ hn' ⟨φ g, hmem g⟩
  have hle : (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0).comap φ ≤
      CFSG.pCore (ringChar K) (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)) :=
    le_sSup ⟨hnormal, (hpg (ringChar K)).comap_of_injective φ hφ⟩
  intro g hg
  have hgQ : (g : ModGL TwistTag.E6.tag K) ∈
      graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0 := hg
  exact ⟨⟨g, (mem_twE6LongRootParabolic_iff σ g).2 (hQP hgQ)⟩, hle hgQ, rfl⟩

theorem twE6LongRootRadical_map_subtype :
    (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
        (twistedE6RootGroup K σ).subtype =
      (CFSG.pCore (ringChar K) (graphFixedParabolic TwistTag.E6 K σ.toRingHom J0)).map
        (graphFixedParabolic TwistTag.E6 K σ.toRingHom J0).subtype := by
  let e : twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ≃*
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 :=
    (Subgroup.equivMapOfInjective _ (twistedE6RootGroup K σ).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (twE6LongRootParabolic_map_subtype σ))
  rw [← CFSG.pCore_map_iso (ringChar K) e, twE6LongRootRadical, Subgroup.map_map, Subgroup.map_map]
  rfl

end Radical

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
