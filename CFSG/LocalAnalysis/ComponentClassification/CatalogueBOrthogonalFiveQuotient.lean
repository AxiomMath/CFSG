module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveKernel
public import Mathlib.GroupTheory.Solvable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveExhaustion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap
open scoped commutatorElement

universe u

variable {K : Type u} [Field K]

@[expose] def selfAdjointSymplecticImage (h2 : (2 : K) ≠ 0) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :=
  (selfAdjointSymplecticAction h2).range

theorem selfAdjointSymplecticImage_eq_map (h2 : (2 : K) ≠ 0) :
    selfAdjointSymplecticImage h2 =
      ((symplecticMultiplier (K := K)).ker.prod (⊥ : Subgroup (rootsOfUnity 2 K))).map
        (selfAdjointFullAction h2) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨(A.val, 1), ?_, ?_⟩
    · exact ⟨A.property, Subgroup.one_mem _⟩
    · change selfAdjointOrthogonalAction h2 A.val * selfAdjointScalarAction 1 = _
      rw [map_one, mul_one]
      rfl
  · rintro ⟨⟨A, ε⟩, hA, rfl⟩
    have hε : ε = 1 := Subgroup.mem_bot.mp hA.2
    refine ⟨⟨A, hA.1⟩, ?_⟩
    change selfAdjointOrthogonalAction h2 A =
      selfAdjointOrthogonalAction h2 A * selfAdjointScalarAction ε
    rw [hε, map_one, mul_one]

instance selfAdjointSymplecticImageNormal (h2 : (2 : K) ≠ 0) :
    (selfAdjointSymplecticImage h2).Normal := by
  rw [selfAdjointSymplecticImage_eq_map]
  exact Subgroup.Normal.map inferInstance _ (selfAdjointFullAction_surjective h2)

theorem symplecticMultiplier_commutator (A B : symplecticSimilitudes K) :
    symplecticMultiplier ⁅A, B⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem selfAdjoint_full_commutator_mem (h2 : (2 : K) ≠ 0)
    (g h : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :
    ⁅g, h⁆ ∈ selfAdjointSymplecticImage h2 := by
  obtain ⟨⟨A, ε⟩, rfl⟩ := selfAdjointFullAction_surjective h2 g
  obtain ⟨⟨B, δ⟩, rfl⟩ := selfAdjointFullAction_surjective h2 h
  rw [← map_commutatorElement]
  have hε : ⁅ε, δ⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm ε δ)
  refine ⟨⟨⁅A, B⁆, symplecticMultiplier_commutator A B⟩, ?_⟩
  change selfAdjointOrthogonalAction h2 ⁅A, B⁆ =
    selfAdjointOrthogonalAction h2 ⁅A, B⁆ * selfAdjointScalarAction ⁅ε, δ⁆
  rw [hε, map_one, mul_one]

theorem selfAdjoint_commutator_le_symplecticImage (h2 : (2 : K) ≠ 0) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) ≤
      selfAdjointSymplecticImage h2 := by
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  exact selfAdjoint_full_commutator_mem h2 g h

instance selfAdjointSymplecticQuotientCommutative (h2 : (2 : K) ≠ 0) :
    IsMulCommutative
      (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) ⧸
        selfAdjointSymplecticImage h2) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (selfAdjoint_commutator_le_symplecticImage h2)

instance selfAdjointSymplecticQuotientSolvable (h2 : (2 : K) ≠ 0) :
    Group.IsSolvable
      (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) ⧸
        selfAdjointSymplecticImage h2) := inferInstance

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
