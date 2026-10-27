module

public import CFSG.ClassicalInvolution.Asc77.AscS16G

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section ZStar

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem zStar_of_hall (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hall : ∀ B ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)),
      IsUniqueInvolution B (T7H.toBar Ω (u₁ * u₂) z (z_mem_layer h))) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
  classical
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) := isPGroup_zpowers_of_sq_eq_one h.sq_12
  have hK₃Ω : K₃ ∈ tqMembers Ω (u₁ * u₂) := S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzY : z ∈ exactLayer Ω (u₁ * u₂) := z_mem_layer h
  set u : G := u₁ * u₂ with hudef
  set Y : Subgroup G := exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := exactLayer_le_centralizer Ω u
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ.conjInvariant hg))
  have hzK₃ : IsUniqueInvolution K₃ z := h.hzK₃
  have hOY : oddCoreOf Y ≤ oddCoreOf C :=
    le_oddCoreIn_of_normalizes ((oddCoreOf_le_self Y).trans hYC) (fun g hg => hOnorm g hg)
      (oddCoreOf_odd_natCard _)
  have hzC : z ∈ C := hYC hzY
  have hcomm : ∀ g ∈ C, ⁅g, z⁆ ∈ oddCoreOf Y := by
    intro g hg
    have hgK₃ : conjSub g K₃ ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hg hK₃Ω
    have hzg : IsUniqueInvolution (conjSub g K₃) (g * z * g⁻¹) := hzK₃.conj g
    have hzgc : g * z * g⁻¹ ∈ exactCore u (conjSub g K₃) :=
      (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hgK₃ hzg).mem
    have hzgY : g * z * g⁻¹ ∈ Y := exactCore_le_exactLayer hgK₃ hzgc
    have hB := hall _ (T7H.exactImg_mem hgK₃)
    have hB' := T7H.exactImg_isUnique hp hΩ hcpg hgK₃ hzg hzgY
    have heq : T7H.toBar Ω u z hzY = T7H.toBar Ω u (g * z * g⁻¹) hzgY := hB.eq hB'
    have hmem : (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨g * z * g⁻¹, hzgY⟩ ∈ N₀ := QuotientGroup.eq.mp heq
    have hmemG : z⁻¹ * (g * z * g⁻¹) ∈ oddCoreOf Y := ⟨_, hmem, rfl⟩
    have hconj := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hzY) hmemG
    have e : z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = ⁅g, z⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at hconj
  refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hc : ⁅(g : G), z⁆ ∈ oddCoreOf C := hOY (hcomm g g.2)
    obtain ⟨hcC, hco⟩ := mem_oddCoreOf_iff.mp hc
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
        (g * ⟨z, hzC⟩ * g⁻¹ * ⟨z, hzC⟩⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hco
    have h1' : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥C) g,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨z, hzC⟩⁆ = 1 := by
      rw [commutatorElement_def]
      simpa only [map_mul, map_inv] using h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1'

theorem layer_zStar (hR1 : Z2NoD8 p) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) :=
  zStar_of_hall h (layer_hall hR1 h hV3 hAall)

end ZStar

end S16

end CFSG.ClassicalInvolution.Asc77
