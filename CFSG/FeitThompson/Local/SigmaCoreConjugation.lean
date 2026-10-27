module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.SupportOfAMaximalSubgroupCoreFamily
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
public import Mathlib.Data.Set.Lattice

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {𝓜 : Set (Subgroup G)} {M : Subgroup G} {g : G}

theorem sigmaCore_map_conj (M : Subgroup G) (g : G) :
    sigmaCore (M.map (MulAut.conj g : G →* G))
      = (sigmaCore M).map (MulAut.conj g : G →* G) := by
  have hσ : sigmaPrimes (M.map (MulAut.conj g : G →* G)) = sigmaPrimes M := by
    rw [← conj_smul_eq_map_conj]; exact sigmaPrimes_conj_smul M g
  rw [sigmaCore_eq_map_piCore, sigmaCore_eq_map_piCore, hσ,
    map_map_subtype_comm (MulAut.conj g) M, map_piCore_of_mulEquiv]

theorem sigmaCore_conj_smul (M : Subgroup G) (g : G) :
    sigmaCore (MulAut.conj g • M) = MulAut.conj g • sigmaCore M := by
  rw [conj_smul_eq_map_conj (X := G), conj_smul_eq_map_conj (X := G), sigmaCore_map_conj]

theorem mem_sigmaCore_map_conj_iff {x : G} :
    x ∈ sigmaCore (M.map (MulAut.conj g : G →* G)) ↔ g⁻¹ * x * g ∈ sigmaCore M := by
  rw [sigmaCore_map_conj]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    simpa [MulAut.conj, mul_assoc] using hy
  · intro h
    refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem coe_sigmaCore_eq_conj_image_of_coe_eq_conj_image {N : Subgroup G}
    (h : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) :
    (sigmaCore N : Set G) = (fun a => g⁻¹ * a * g) '' (sigmaCore M : Set G) := by
  have hN : N = MulAut.conj g⁻¹ • M := SetLike.coe_injective (by rw [h, coe_conj_inv_smul])
  rw [hN, sigmaCore_conj_smul, coe_conj_inv_smul]

theorem conj_image_coreFamilySupport_sigmaCore
    (h𝓜 : ∀ M ∈ 𝓜, ∀ c : G, M.map (MulAut.conj c : G →* G) ∈ 𝓜) (g : G) :
    (fun x => g⁻¹ * x * g) '' coreFamilySupport 𝓜 sigmaCore
      = coreFamilySupport 𝓜 sigmaCore := by
  have key : ∀ (c : G) (y : G), y ∈ coreFamilySupport 𝓜 sigmaCore →
      c⁻¹ * y * c ∈ coreFamilySupport 𝓜 sigmaCore := by
    intro c y hy
    rw [mem_coreFamilySupport_iff] at hy ⊢
    obtain ⟨M, hM, hyS, hy1⟩ := hy
    refine ⟨M.map (MulAut.conj c⁻¹ : G →* G), h𝓜 M hM c⁻¹, ?_, ?_⟩
    · rw [mem_sigmaCore_map_conj_iff,
        show (c⁻¹)⁻¹ * (c⁻¹ * y * c) * c⁻¹ = y from by group]
      exact hyS
    · simp only [ne_eq, mul_eq_one_iff_eq_inv]
      exact fun h => hy1 (by simpa using h)
  refine Set.eq_of_subset_of_subset ?_ fun y hy => ⟨g * y * g⁻¹, ?_, by group⟩
  · rintro _ ⟨x, hx, rfl⟩; exact key g x hx
  · simpa using key g⁻¹ y hy

omit [Finite G] in
theorem map_conj_mem_setOf_isCoatom (hM : M ∈ {M : Subgroup G | IsCoatom M}) (g : G) :
    M.map (MulAut.conj g : G →* G) ∈ {M : Subgroup G | IsCoatom M} := by
  simp only [Set.mem_setOf_eq] at hM ⊢
  exact isCoatom_map_conj hM g

theorem conj_image_coreFamilySupport_sigmaCore_isCoatom (g : G) :
    (fun x => g⁻¹ * x * g) '' coreFamilySupport {M : Subgroup G | IsCoatom M} sigmaCore
      = coreFamilySupport {M : Subgroup G | IsCoatom M} sigmaCore :=
  conj_image_coreFamilySupport_sigmaCore (fun _ hM c => map_conj_mem_setOf_isCoatom hM c) g

theorem sigmaPrimes_and_sigmaCore_conj_of_isCoatom (_hodd : Odd (Nat.card G))
    (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (_hM : IsCoatom M) {N : Subgroup G}
    (hN : (N : Set G) = (fun a => g⁻¹ * a * g) '' (M : Set G)) :
    sigmaPrimes N = sigmaPrimes M ∧
      (sigmaCore N : Set G) = (fun a => g⁻¹ * a * g) '' (sigmaCore M : Set G) ∧
      (fun x => g⁻¹ * x * g) '' coreFamilySupport {M : Subgroup G | IsCoatom M} sigmaCore
        = coreFamilySupport {M : Subgroup G | IsCoatom M} sigmaCore :=
  ⟨sigmaPrimes_eq_of_coe_eq_conj_image hN,
    coe_sigmaCore_eq_conj_image_of_coe_eq_conj_image hN,
    conj_image_coreFamilySupport_sigmaCore_isCoatom g⟩

end

end CFSG.FeitThompson
