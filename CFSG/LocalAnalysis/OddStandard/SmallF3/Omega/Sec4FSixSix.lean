module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTri
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem sec4F_type_six_of_conj (I : Sec4FInputs) {T : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G T L S z) (hnot : ¬ ∃ h : G, h⁻¹ * T * h = T * z)
    {c : G} (hc : c ≠ 1) (hcy : c * T = T * c)
    (hyc : ∃ g : G, T * c = g⁻¹ * T * g) :
    ∃ α : ℤˣ, InducesTypeSome L c 7 1 6 α := by
  have hL : IsOmega7Group L := sec4_isOmega7Group hctx.toSec4Setting
  have hsc : T * c ∈ centralizer ({T} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, hcy]
  have hst : T * c ≠ T := by
    intro h
    have h1 : T * c = T * 1 := by simpa [mul_one] using h
    exact hc (mul_left_cancel h1)
  rcases sec4_conj_tri I.h36 I.h39 I.h42 I.h43 I.hf43c I.hf214 I.hin6 I.hk6
      hctx hyc hsc hst with htz | ⟨u, _huL, _hu2, hu6, hsu⟩ | h6
  · exact absurd htz hnot
  · refine ⟨-1, ?_⟩
    rw [mul_left_cancel hsu]
    exact hu6
  · refine ⟨1, ?_⟩
    have hcT : T ∈ centralizer (L : Set G) := sec4_t_mem_centralizer hctx.toSec3Setting
    rw [← hcy] at h6
    exact (sec4F_type_mul_cent_iff hL hcT (Or.inr (Or.inr rfl))).mp h6

theorem sec4F_sixsix_contra (I : Sec4FInputs) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) (hnot : ¬ ∃ h : G, h⁻¹ * t * h = t * z) {y c₁ c₂ : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hc₁ : c₁ ≠ 1) (hc₂ : c₂ ≠ 1)
    (hc₁y : c₁ * y = y * c₁) (hc₂y : c₂ * y = y * c₂) (hc₁₂ : c₁ * c₂ = c₂ * c₁)
    (hyc₁ : ∃ g : G, y * c₁ = g⁻¹ * t * g) (hyc₂ : ∃ g : G, y * c₂ = g⁻¹ * t * g)
    (hz : ∃ g : G, c₁ * c₂ = g⁻¹ * z * g) : False := by
  obtain ⟨g₀, rfl⟩ := hy
  let L' : Subgroup G := CFSG.conjugate L g₀
  let z' : G := g₀⁻¹ * z * g₀
  have hctx' : Sec4Ctx G (g₀⁻¹ * t * g₀) L' (CFSG.conjugate S g₀) z' := hctx.conjugate g₀
  have hL' : IsOmega7Group L' := sec4_isOmega7Group hctx'.toSec4Setting
  have hyC : (g₀⁻¹ * t * g₀) ∈ centralizer (L' : Set G) :=
    sec4_t_mem_centralizer hctx'.toSec3Setting
  have hnot' : ¬ ∃ h : G, h⁻¹ * (g₀⁻¹ * t * g₀) * h = (g₀⁻¹ * t * g₀) * z' := by
    rintro ⟨h, hh⟩
    apply hnot
    refine ⟨g₀ * h * g₀⁻¹, ?_⟩
    have hh' := congrArg (fun x => g₀ * x * g₀⁻¹) hh
    simp only [z'] at hh'
    calc (g₀ * h * g₀⁻¹)⁻¹ * t * (g₀ * h * g₀⁻¹)
        = g₀ * (h⁻¹ * (g₀⁻¹ * t * g₀) * h) * g₀⁻¹ := by group
      _ = g₀ * ((g₀⁻¹ * t * g₀) * z') * g₀⁻¹ := hh'
      _ = t * z := by simp only [z']; group
  have hconv₁ : ∃ g : G, (g₀⁻¹ * t * g₀) * c₁ = g⁻¹ * (g₀⁻¹ * t * g₀) * g := by
    obtain ⟨g, hg⟩ := hyc₁
    refine ⟨g₀⁻¹ * g, ?_⟩
    rw [hg]
    group
  have hconv₂ : ∃ g : G, (g₀⁻¹ * t * g₀) * c₂ = g⁻¹ * (g₀⁻¹ * t * g₀) * g := by
    obtain ⟨g, hg⟩ := hyc₂
    refine ⟨g₀⁻¹ * g, ?_⟩
    rw [hg]
    group
  have htype₁ : ∃ α : ℤˣ, InducesTypeSome L' c₁ 7 1 6 α :=
    sec4F_type_six_of_conj I hctx' hnot' hc₁ hc₁y hconv₁
  have htype₂ : ∃ α : ℤˣ, InducesTypeSome L' c₂ 7 1 6 α :=
    sec4F_type_six_of_conj I hctx' hnot' hc₂ hc₂y hconv₂
  have hmem : c₁ * c₂ ∈ centralizer ({(g₀⁻¹ * t * g₀)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, hc₂y, ← mul_assoc, hc₁y, mul_assoc]
  obtain ⟨g, hg⟩ := hz
  have hgz : (g₀⁻¹ * g)⁻¹ * z' * (g₀⁻¹ * g) = c₁ * c₂ := by
    rw [hg]
    simp only [z']
    group
  have hmem' : (g₀⁻¹ * g)⁻¹ * z' * (g₀⁻¹ * g) ∈
      centralizer ({(g₀⁻¹ * t * g₀)} : Set G) := by
    rw [hgz]
    exact hmem
  have h43res := I.h43 G (g₀⁻¹ * t * g₀) L' (CFSG.conjugate S g₀) z' hctx'
    (g₀⁻¹ * g) hmem'
  rw [hgz] at h43res
  obtain ⟨α, hα⟩ := htype₁
  obtain ⟨β, hβ⟩ := htype₂
  rcases h43res with ⟨l, hl, hl_eq⟩ | ⟨l, hl, hl_eq⟩
  · exact I.h66 G L' hL' c₁ c₂ α β hc₁₂ hα hβ (l * z' * l⁻¹) 1
      (IsI4PlusIn.conj_of_mem hctx'.pocket hl) (Subgroup.one_mem _)
      (by rw [hl_eq, mul_one])
  · have hw_mem : l * z' * l⁻¹ ∈ L' := mul_mem (mul_mem hl hctx'.pocket.mem) (inv_mem hl)
    have hTw : (l * z' * l⁻¹) * (g₀⁻¹ * t * g₀) = (g₀⁻¹ * t * g₀) * (l * z' * l⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hyC (l * z' * l⁻¹) hw_mem
    have hTl : l * (g₀⁻¹ * t * g₀) = (g₀⁻¹ * t * g₀) * l :=
      Subgroup.mem_centralizer_iff.mp hyC l hl
    have heq : c₁ * c₂ = (l * z' * l⁻¹) * (g₀⁻¹ * t * g₀) := by
      rw [hl_eq]
      calc l * ((g₀⁻¹ * t * g₀) * z') * l⁻¹
          = (l * (g₀⁻¹ * t * g₀)) * z' * l⁻¹ := by group
        _ = ((g₀⁻¹ * t * g₀) * l) * z' * l⁻¹ := by rw [hTl]
        _ = (g₀⁻¹ * t * g₀) * (l * z' * l⁻¹) := by group
        _ = (l * z' * l⁻¹) * (g₀⁻¹ * t * g₀) := hTw.symm
    exact I.h66 G L' hL' c₁ c₂ α β hc₁₂ hα hβ (l * z' * l⁻¹) (g₀⁻¹ * t * g₀)
      (IsI4PlusIn.conj_of_mem hctx'.pocket hl) hyC heq

end CFSG.OddStandard.SmallF3.Omega
