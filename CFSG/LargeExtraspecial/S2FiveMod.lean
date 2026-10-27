module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2

namespace S2

variable {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]

@[expose] def fixAll {X : Type*} [Group X] (ρ : X →* (N ≃ₗ[ZMod 2] N)) :
    Submodule (ZMod 2) N where
  carrier := {v | ∀ g, ρ g v = v}
  add_mem' {u v} hu hv g := by rw [map_add, hu g, hv g]
  zero_mem' g := map_zero _
  smul_mem' c v hv g := by rw [map_smul, hv g]

theorem mem_fixAll {X : Type*} [Group X] {ρ : X →* (N ≃ₗ[ZMod 2] N)} {v : N} :
    v ∈ fixAll ρ ↔ ∀ g, ρ g v = v :=
  Iff.rfl

variable [FiniteDimensional (ZMod 2) N]

theorem finrank_le_finrank_iInf_add {ι : Type*} [Fintype ι] (x : ι → N ≃ₗ[ZMod 2] N)
    (h : ∀ i, finrank (ZMod 2) (commSpace (x i)) ≤ 1) :
    finrank (ZMod 2) N ≤ finrank (ZMod 2) ↥(⨅ i, fixSpace (x i)) + Fintype.card ι := by
  let Φ : N →ₗ[ZMod 2] ((i : ι) → commSpace (x i)) :=
    LinearMap.pi fun i => ((x i : N →ₗ[ZMod 2] N) - 1).rangeRestrict
  have hker : LinearMap.ker Φ = ⨅ i, fixSpace (x i) := by
    rw [LinearMap.ker_pi]
    congr 1
    ext i : 1
    exact LinearMap.ker_rangeRestrict _
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 := Submodule.finrank_le (LinearMap.range Φ)
  rw [Module.finrank_pi_fintype] at h2
  have h3 : ∑ i, finrank (ZMod 2) (commSpace (x i)) ≤ Fintype.card ι := by
    calc ∑ i, finrank (ZMod 2) (commSpace (x i)) ≤ ∑ _i : ι, 1 :=
          Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι := by simp
  rw [hker] at h1
  omega

end S2

end CFSG.LargeExtraspecial
