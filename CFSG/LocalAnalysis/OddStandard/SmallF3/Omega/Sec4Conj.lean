module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem IsSylow2Of.conjugate {S H : Subgroup G} (h : IsSylow2Of S H) (g : G) :
    IsSylow2Of (CFSG.conjugate S g) (CFSG.conjugate H g) := by
  obtain ⟨hle, hp, hndvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.map _, ?_⟩
  rw [CFSG.conjugate, CFSG.conjugate,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
  exact hndvd

theorem IsI4PlusIn.conj_of_mem {L : Subgroup G} {z l : G} (h : IsI4PlusIn L z) (hl : l ∈ L) :
    IsI4PlusIn L (l * z * l⁻¹) := by
  have h1 := h.conjugate l⁻¹
  have h2 : CFSG.conjugate L l⁻¹ = L := by
    ext x
    rw [mem_conjugate_iff, inv_inv]
    exact ⟨fun hx => by simpa [mul_assoc] using mul_mem (mul_mem hl hx) (inv_mem hl),
      fun hx => mul_mem (mul_mem (inv_mem hl) hx) hl⟩
  rwa [h2, inv_inv] at h1

theorem Sec4Setting.conjugate [Finite G] {t : G} {L : Subgroup G} (h : Sec4Setting G t L)
    (g : G) : Sec4Setting G (g⁻¹ * t * g) (CFSG.conjugate L g) :=
  { toSec3SettingLB := h.toSec3SettingLB.conjugate g
    omega7 := lieModel_quotient_oddCore_conjugate g h.omega7 }

theorem Asc82Notation.conjugate {t : G} {L S : Subgroup G} {z : G} (h : Asc82Notation t L S z)
    (g : G) : Asc82Notation (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← conjugate_centralizer_singleton t g]
    exact h.sylow.conjugate g
  · rw [mem_conjugate_iff]
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact h.mem_S
  · intro s hs
    rw [mem_conjugate_iff] at hs
    have hc : (g * s * g⁻¹) * z = z * (g * s * g⁻¹) := h.central (g * s * g⁻¹) hs
    have hc' := congrArg (fun x => g⁻¹ * x * g) hc
    rwa [show g⁻¹ * (g * s * g⁻¹ * z) * g = s * (g⁻¹ * z * g) by group,
      show g⁻¹ * (z * (g * s * g⁻¹)) * g = (g⁻¹ * z * g) * s by group] at hc'
  · exact h.pocket.conjugate g

theorem Sec4Ctx.conjugate [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec4Ctx G t L S z)
    (g : G) : Sec4Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := by
  exact ⟨h.toSec4Setting.conjugate g, h.toAsc82Notation.conjugate g⟩

end CFSG.OddStandard.SmallF3.Omega
