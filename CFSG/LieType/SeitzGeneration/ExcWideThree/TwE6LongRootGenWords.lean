module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd
public import CFSG.LieType.Chevalley.ParabolicRadicalLeviRoots
public import CFSG.LieType.Chevalley.GraphFixedParabolicRootFactors

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Pure

@[expose] def genWord : Fin TwistTag.E6.foldedTag.rank → List (Fin TwistTag.E6.foldedTag.rank)
  | 0 => [3, 2, 1]
  | 1 => [3, 2]
  | 2 => [3]
  | 3 => []

@[expose] def genVec (a : Fin TwistTag.E6.foldedTag.rank) (i : Fin TwistTag.E6.tag.rank) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  (genWord a).foldr (fun b w => (TwistTag.E6.orbitWord b).foldr (reflect TwistTag.E6.tag) w)
    (Pi.single i 1)

private theorem genVec_check :
    ∀ a : Fin TwistTag.E6.foldedTag.rank, ∀ i : Fin TwistTag.E6.tag.rank,
      i ∈ TwistTag.E6.orbit a → 0 < height (genVec a i) ∧ genVec a i 1 ≠ 0 := by
  decide +kernel

private theorem isRoot_genVec (a : Fin TwistTag.E6.foldedTag.rank)
    (i : Fin TwistTag.E6.tag.rank) : IsRoot TwistTag.E6.tag (genVec a i) := by
  have key : ∀ ω : List (Fin TwistTag.E6.tag.rank), ∀ {v : Fin TwistTag.E6.tag.rank → ℤ},
      IsRoot TwistTag.E6.tag v →
        IsRoot TwistTag.E6.tag (ω.foldr (reflect TwistTag.E6.tag) v) := by
    intro ω
    induction ω with
    | nil => exact fun h => h
    | cons j ω ih => exact fun h => IsRoot.reflect j (ih h)
  unfold genVec
  induction genWord a with
  | nil => exact IsRoot.basis i
  | cons b l ih => exact key _ ih

private theorem one_notMem_orbitUnion_J0 :
    (1 : Fin TwistTag.E6.tag.rank) ∉ TwistTag.E6.orbitUnion J0 := by
  rw [TwistTag.mem_orbitUnion]
  rintro ⟨a, ha, hi⟩
  have ha' : a ≠ a2 := ha
  exact ha' (((TwistTag.mem_orbit_iff TwistTag.E6).1 hi).symm.trans (by decide))

private theorem genVec_mem_parabolicRadicalRoots {a : Fin TwistTag.E6.foldedTag.rank}
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    genVec a i ∈ parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0) :=
  mem_parabolicRadicalRoots_iff.2 ⟨isRoot_genVec a i, (genVec_check a i hi).1, 1,
    one_notMem_orbitUnion_J0, (genVec_check a i hi).2⟩

end Pure

section Weyl


@[expose] def genU (a : Fin TwistTag.E6.foldedTag.rank) : WeylGroup TwistTag.E6.tag :=
  ((genWord a).map TwistTag.E6.orbitReflection).prod

theorem genU_mem (a : Fin TwistTag.E6.foldedTag.rank) : genU a ∈ relWeylTwist TwistTag.E6 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact TwistTag.E6.orbitReflection_mem b

private theorem genU_smul_single (a : Fin TwistTag.E6.foldedTag.rank)
    (i : Fin TwistTag.E6.tag.rank) :
    genU a • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = genVec a i := by
  rw [genU, prod_orbitReflection_smul]
  rfl

theorem image_genU_smul_subset (a : Fin TwistTag.E6.foldedTag.rank) :
    ((fun i => genU a • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) ''
      ↑(TwistTag.E6.orbit a)) ⊆
        parabolicRadicalRoots TwistTag.E6.tag (TwistTag.E6.orbitUnion J0) := by
  rintro _ ⟨i, hi, rfl⟩
  dsimp only
  rw [genU_smul_single]
  exact genVec_mem_parabolicRadicalRoots hi

end Weyl

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen
