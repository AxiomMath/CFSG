module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.CommutatorDimension
public import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.ExtraspecialDimensionDivisibility

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

open Subgroup

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

open scoped Classical in
theorem extraspecial_center_commutator_decomposition_and_dimension_bounds [Finite G] [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup G) (hH : CFSG.IsExtraspecialPGroup p H) (hexp : Monoid.exponent H = p)
    (hwidth : Nat.card H = p ^ (1 + 2 * n))
    (X : Subgroup G) (hXH : X ≤ H) (hXp : Nat.card X = p) (hXZ : X ≠ centerIn H) :
    let U : Submodule (ZMod 2) V := commSpace ρ (centerIn H)
    let m : ℕ := Module.finrank (ZMod 2) ↥(U ⊓ fixedSpace ρ X)
    (iSupIndep (fun Y : conjClass H X => U ⊓ fixedSpace ρ (Y : Subgroup G)) ∧
      (⨆ Y : conjClass H X, U ⊓ fixedSpace ρ (Y : Subgroup G)) = U) ∧
    Module.finrank (ZMod 2) U = m * p ∧
    Module.finrank (ZMod 2) ↥(commOn ρ X U) = m * (p - 1) ∧
    (∀ t : G, orderOf t = 2 → (∀ x ∈ X, t * x * t⁻¹ = x⁻¹) →
      m * (p - 1) ≤ 2 * Module.finrank (ZMod 2) ↥(commSpace ρ (zpowers t))) ∧
    p ^ (n - 1) * WeakClosure.dOfPrime p ∣ m := by
  intro U m
  have hU : ∀ x ∈ X, ∀ u ∈ U, ρ x u ∈ U := by
    intro x hx
    have hxH : x ∈ H := hXH hx
    have hle : commSpace ρ (centerIn H) ≤
        Submodule.comap (ρ x) (commSpace ρ (centerIn H)) := by
      unfold commSpace
      rw [Submodule.span_le]
      rintro w ⟨z, hz, v, rfl⟩
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
      have hzk : z = (k : G) := hkz.symm
      subst hzk
      have hcomm : (x : G) * (k : G) = (k : G) * x := by
        have := (Subgroup.mem_center_iff.mp hk) ⟨x, hxH⟩
        exact congrArg Subtype.val this
      have hc : ρ x * ρ (k : G) = ρ (k : G) * ρ x := by
        rw [← map_mul, ← map_mul, hcomm]
      have e1 : ρ x (ρ (k : G) v) = ρ (k : G) (ρ x v) :=
        congrArg (fun f : V →ₗ[ZMod 2] V => f v) hc
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e1]
      exact Submodule.subset_span ⟨(k : G), Subgroup.mem_map_of_mem H.subtype hk, ρ x v, rfl⟩
    exact hle
  have h1 := ExtraspecialModuleDecomposition.iSupIndep_and_iSup_eq hp hp2 H hH hexp ρ X hXH hXp hXZ
  have h2 := ExtraspecialModuleDecomposition.finrank_commSpace hp hp2 H hH hexp ρ X hXH hXp hXZ
  have h3 := CommutatorDimension.dimension_formula ρ hp hp2 X hXp U hU
    (by rw [h2, Nat.mul_comm]) rfl
  have h5 := CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.finrank_commOn_le ρ X U
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro t ht hinv
    have h4 := CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.finrank_commSpace_le_two_mul ρ hp hp2 X hXp t ht hinv
    exact (le_of_eq h3.symm).trans (h5.trans h4)
  · exact ExtraspecialDimensionDivisibility.dimension_dvd ρ hρ hp hp2 H hH hexp hwidth X hXH hXp hXZ

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
