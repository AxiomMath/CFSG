module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightCTwoElementary

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem tauSet_alt_eq_union {G : Type*} [Group G] {L : Subgroup G} {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) :
    tauSet φ e (fun B => ∀ i, B i i = 0) =
      {1} ∪ tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) := by
  ext x
  rw [Set.mem_union, Set.mem_singleton_iff, mem_tauSet_iff φ he, mem_tauSet_iff φ he]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases hB0 : Multiplicative.toAdd B = 0
    · left
      rw [show B = 1 from Multiplicative.toAdd.injective hB0, map_one]
    · right
      refine ⟨B, (sym_rank_two_alternating_iff _).2 ?_, rfl⟩
      have hBa := eq_altLabel_of_diag_eq_zero (B := Multiplicative.toAdd B) (funext hB)
      refine ⟨_, fun h => hB0 ?_, congrArg Subtype.val hBa⟩
      rw [hBa, h, DegreeEight.altLabel_zero]
  · rintro (rfl | ⟨B, hB, rfl⟩)
    · exact ⟨1, fun i => rfl, map_one _⟩
    · exact ⟨B, hB.2, rfl⟩

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem tauSet_alt_eq_radI :
    tauSet φ e (fun B => ∀ i, B i i = 0) =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G) := by
  ext x
  rw [mem_tauSet_iff φ he, SetLike.mem_coe, BinarySymThreeOrbit.mem_layerSub θ₂]
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨Multiplicative.toAdd B, BinarySymThreeOrbit.mem_altSym_iff.2 (funext hB), ?_⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one]
    rfl
  · rintro ⟨B, hB, rfl⟩
    refine ⟨Multiplicative.ofAdd B, fun i => congrFun (BinarySymThreeOrbit.mem_altSym_iff.1 hB) i,
      ?_⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he in
theorem altOrbit_of_eq (halt : conjClass 𝒩 z = z • tauSet φ e (fun B => ∀ i, B i i = 0)) :
    AltOrbit z φ e := by
  change conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)
  rw [halt, tauSet_alt_eq_union φ he, Set.smul_set_union, Set.smul_set_singleton, smul_eq_mul,
    mul_one]

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
