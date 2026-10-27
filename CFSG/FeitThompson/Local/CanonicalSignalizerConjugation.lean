module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.CanonicalCentralizerSignalizerFrom
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {𝓜 : Set (Subgroup G)} {S : Subgroup G → Subgroup G}

structure IsConjStableCoreFamily (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) : Prop where
  mem_conj_smul : ∀ M ∈ 𝓜, ∀ c : G, MulAut.conj c • M ∈ 𝓜
  map_conj_smul : ∀ M ∈ 𝓜, ∀ c : G, S (MulAut.conj c • M) = MulAut.conj c • S M

variable (h𝓜 : IsConjStableCoreFamily 𝓜 S)

include h𝓜 in
theorem supportingMaximals_conj_smul (x g : G) :
    supportingMaximals 𝓜 S (MulAut.conj g • x)
      = (fun M => MulAut.conj g • M) '' supportingMaximals 𝓜 S x := by
  ext M
  simp only [Set.mem_image, mem_supportingMaximals]
  constructor
  · rintro ⟨hM, hxM⟩
    refine ⟨MulAut.conj g⁻¹ • M, ⟨h𝓜.mem_conj_smul M hM g⁻¹, ?_⟩, ?_⟩
    · rw [h𝓜.map_conj_smul M hM g⁻¹, mem_conj_smul_iff]
      simpa [MulAut.smul_def, MulAut.conj, mul_assoc] using hxM
    · rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  · rintro ⟨M₀, ⟨hM₀, hx⟩, rfl⟩
    refine ⟨h𝓜.mem_conj_smul M₀ hM₀ g, ?_⟩
    rw [h𝓜.map_conj_smul M₀ hM₀ g, mem_conj_smul_iff]
    simpa [MulAut.smul_def, MulAut.conj, mul_assoc] using hx

include h𝓜 in
theorem supportMultiplicity_conj (x g : G) :
    supportMultiplicity 𝓜 S (g⁻¹ * x * g) = supportMultiplicity 𝓜 S x := by
  have hx : g⁻¹ * x * g = MulAut.conj g⁻¹ • x := by simp [MulAut.smul_def, MulAut.conj, mul_assoc]
  rw [hx, supportMultiplicity_eq_ncard, supportMultiplicity_eq_ncard,
    supportingMaximals_conj_smul h𝓜 x g⁻¹,
    Set.ncard_image_of_injective _ (MulAction.injective (MulAut.conj g⁻¹))]

section Finite

variable [Finite G]

omit h𝓜 in
theorem map_subtype_piCore_of_eq_map {H K : Subgroup G} (φ : G ≃* G)
    (h : K = H.map (φ : G →* G)) (π : Set ℕ) :
    (piCore π K).map K.subtype = ((piCore π H).map H.subtype).map (φ : G →* G) := by
  subst h
  rw [map_map_subtype_comm, map_piCore_of_mulEquiv]

include h𝓜 in
theorem canonicalSignalizer_conj_smul (x g : G) :
    canonicalSignalizer 𝓜 S (MulAut.conj g • x)
      = MulAut.conj g • canonicalSignalizer 𝓜 S x := by
  have hC : Subgroup.centralizer ({MulAut.conj g • x} : Set G)
      = (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g : G →* G) := by
    rw [← conj_smul_eq_map_conj, smul_centralizer_singleton]
    simp [MulAut.smul_def, MulAut.conj]
  have hk : supportMultiplicity 𝓜 S (MulAut.conj g • x) = supportMultiplicity 𝓜 S x := by
    have h := supportMultiplicity_conj h𝓜 x g⁻¹
    simpa [MulAut.smul_def, MulAut.conj, mul_assoc] using h
  rw [canonicalSignalizer_eq 𝓜 S (MulAut.conj g • x), canonicalSignalizer_eq 𝓜 S x, hk,
    conj_smul_eq_map_conj]
  exact map_subtype_piCore_of_eq_map (MulAut.conj g) hC _

include h𝓜 in
theorem canonicalSignalizer_map_conj (x g : G) :
    canonicalSignalizer 𝓜 S (g * x * g⁻¹)
      = (canonicalSignalizer 𝓜 S x).map (MulAut.conj g : G →* G) := by
  rw [← conj_smul_eq_map_conj,
    show g * x * g⁻¹ = MulAut.conj g • x from by simp [MulAut.smul_def, MulAut.conj]]
  exact canonicalSignalizer_conj_smul h𝓜 x g

include h𝓜 in
theorem coe_canonicalSignalizer_conj_image (x g : G) :
    (canonicalSignalizer 𝓜 S (g⁻¹ * x * g) : Set G)
      = (fun a => g⁻¹ * a * g) '' (canonicalSignalizer 𝓜 S x : Set G) := by
  rw [show g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ from by simp,
    canonicalSignalizer_map_conj h𝓜 x g⁻¹, Subgroup.coe_map,
    show ((MulAut.conj g⁻¹ : G →* G) : G → G) = (fun a => g⁻¹ * a * g) from by
      funext a; simp [MulAut.conj]]

omit h𝓜 [Finite G] in
theorem conj_image_smul_set (x g : G) (s : Set G) :
    (fun a => g⁻¹ * a * g) '' (x • s) = (g⁻¹ * x * g) • ((fun a => g⁻¹ * a * g) '' s) := by
  rw [show (fun a : G => g⁻¹ * a * g) = ((MulAut.conj g⁻¹ : G →* G) : G → G) from by
    funext a; simp [MulAut.conj], Set.image_smul_distrib]
  simp [MulAut.conj]

include h𝓜 in
theorem conj_image_smul_coe_canonicalSignalizer (x g : G) :
    (fun a => g⁻¹ * a * g) '' (x • (canonicalSignalizer 𝓜 S x : Set G))
      = (g⁻¹ * x * g) • (canonicalSignalizer 𝓜 S (g⁻¹ * x * g) : Set G) := by
  rw [conj_image_smul_set, coe_canonicalSignalizer_conj_image h𝓜]

end Finite

theorem conj_smul_mem_setOf_isCoatom {M : Subgroup G} (hM : M ∈ {M : Subgroup G | IsCoatom M})
    (c : G) : MulAut.conj c • M ∈ {M : Subgroup G | IsCoatom M} := by
  rw [Set.mem_ofPred_eq, conj_smul_eq_map_conj]
  exact isCoatom_map_conj hM c

theorem isConjStableCoreFamily_sigmaCore [Finite G] :
    IsConjStableCoreFamily {M : Subgroup G | IsCoatom M} sigmaCore where
  mem_conj_smul _ hM c := conj_smul_mem_setOf_isCoatom hM c
  map_conj_smul M _ c := sigmaCore_conj_smul M c

section Sigma

variable [Finite G] (x g : G)

theorem supportMultiplicity_sigmaCore_conj :
    supportMultiplicity {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g)
      = supportMultiplicity {M : Subgroup G | IsCoatom M} sigmaCore x :=
  supportMultiplicity_conj isConjStableCoreFamily_sigmaCore x g

theorem canonicalSignalizer_sigmaCore_conj :
    canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore (MulAut.conj g • x)
      = MulAut.conj g • canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x :=
  canonicalSignalizer_conj_smul isConjStableCoreFamily_sigmaCore x g

theorem coe_canonicalSignalizer_sigmaCore_conj_image :
    (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g) : Set G)
      = (fun a => g⁻¹ * a * g) ''
        (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x : Set G) :=
  coe_canonicalSignalizer_conj_image isConjStableCoreFamily_sigmaCore x g

theorem conj_image_smul_coe_canonicalSignalizer_sigmaCore :
    (fun a => g⁻¹ * a * g) ''
        (x • (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x : Set G))
      = (g⁻¹ * x * g) •
        (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g) : Set G) :=
  conj_image_smul_coe_canonicalSignalizer isConjStableCoreFamily_sigmaCore x g

end Sigma

theorem supportMultiplicity_and_canonicalSignalizer_conj_of_isCoatom [Finite G]
    (_hodd : Odd (Nat.card G)) (_hsimple : IsSimpleGroup G) (_hna : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {x : G}
    (_hx : x ∈ coreFamilySupport {M : Subgroup G | IsCoatom M} sigmaCore) (g : G) :
    supportMultiplicity {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g)
        = supportMultiplicity {M : Subgroup G | IsCoatom M} sigmaCore x ∧
      (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g) : Set G)
        = (fun a => g⁻¹ * a * g) ''
          (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x : Set G) ∧
      (fun a => g⁻¹ * a * g) ''
          (x • (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore x : Set G))
        = (g⁻¹ * x * g) •
          (canonicalSignalizer {M : Subgroup G | IsCoatom M} sigmaCore (g⁻¹ * x * g) : Set G) :=
  ⟨supportMultiplicity_sigmaCore_conj x g, coe_canonicalSignalizer_sigmaCore_conj_image x g,
    conj_image_smul_coe_canonicalSignalizer_sigmaCore x g⟩

end

end CFSG.FeitThompson
