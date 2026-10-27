module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Q1


theorem isPGroup_multiplicative (K : Type) [Field K] [Finite K] :
    IsPGroup (ringChar K) (Multiplicative K) := fun x => ⟨1, by
  rw [pow_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
  rfl⟩

theorem isPGroup_rootSubgroup (K : Type) [Field K] [Finite K] (β : Fin TwistTag.E6.tag.rank → ℤ) :
    IsPGroup (ringChar K) (rootSubgroup TwistTag.E6.tag K β) :=
  (isPGroup_multiplicative K).of_equiv (rootSubgroupEquiv TwistTag.E6.tag K β)

theorem isPGroup_twE6RootSubgroup {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (β : Fin TwistTag.E6.tag.rank → ℤ) :
    IsPGroup (ringChar K) (twE6RootSubgroup K σ β) :=
  (isPGroup_rootSubgroup K β).comap_of_injective (twistedE6RootGroup K σ).subtype
    Subtype.val_injective

theorem le_radical_of_isPGroup {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (X : Subgroup (twistedE6RootGroup K σ)) (hX : IsPGroup (ringChar K) X) :
    X ≤ twE6LongRootRadical X := by
  intro x hx
  have hxP : x ∈ twE6LongRootParabolic X := Subgroup.le_normalizer hx
  have hN : (X.subgroupOf (twE6LongRootParabolic X)).Normal := Subgroup.normal_in_normalizer
  have hpg : IsPGroup (ringChar K) (X.subgroupOf (twE6LongRootParabolic X)) :=
    hX.comap_of_injective (twE6LongRootParabolic X).subtype Subtype.val_injective
  have hle : X.subgroupOf (twE6LongRootParabolic X) ≤
      CFSG.pCore (ringChar K) (twE6LongRootParabolic X) :=
    le_sSup ⟨hN, hpg⟩
  exact ⟨⟨x, hxP⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem q1_holds : TwE6LongRootParabolicStructure := by
  intro K _ _ σ q _ _ _ X Xm hpair
  obtain ⟨g, rfl, rfl⟩ := hpair
  exact le_radical_of_isPGroup _ ((isPGroup_twE6RootSubgroup σ e6HighestRoot).map _)

end Q1

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
