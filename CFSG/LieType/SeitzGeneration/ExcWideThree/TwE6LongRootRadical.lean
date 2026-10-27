module

public import CFSG.LieType.Chevalley.GraphFixedParabolicPCore
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Radical

@[expose] def radicalWord : List (Fin TwistTag.E6.foldedTag.rank) := [0, 1, 2, 0, 1, 2, 0, 1, 2]

private theorem radicalWord_mem_J0 : ∀ a ∈ radicalWord, a ∈ J0 := by
  have h : ∀ a ∈ radicalWord, a ≠ a2 := by decide
  exact h

private theorem radicalWord_neg_height :
    ∀ α ∈ rootFinset TwistTag.E6.tag, α 1 = 0 → 0 < height α →
      height (radicalWord.foldr
        (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) α) < 0 := by
  decide +kernel

private theorem height_radicalWord_smul_neg {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ parabolicPosRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0)) :
    height ((radicalWord.map TwistTag.E6.orbitReflection).prod • α) < 0 := by
  rw [prod_orbitReflection_smul]
  refine radicalWord_neg_height α (mem_rootFinset.2 hα.1.1) (hα.1.2 1 ?_) hα.2.2
  rw [TwistTag.mem_orbitUnion]
  rintro ⟨a, ha, h1⟩
  have key : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ a2 →
      (1 : Fin TwistTag.E6.tag.rank) ∉ TwistTag.E6.orbit a := by
    decide
  exact key a ha h1

theorem pCore_graphFixedParabolic_le (K : Type) [Field K] [Finite K] (σ : K ≃+* K) :
    (CFSG.pCore (ringChar K) (graphFixedParabolic TwistTag.E6 K σ.toRingHom J0)).map
        (graphFixedParabolic TwistTag.E6 K σ.toRingHom J0).subtype ≤
      graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0 :=
  pCore_graphFixedParabolic_le_of_word TwistTag.E6 K σ J0 radicalWord radicalWord_mem_J0
    fun _ hα => height_radicalWord_smul_neg hα

end Radical

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
