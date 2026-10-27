module

public import CFSG.ClassicalInvolution.Asc77.AscS16C
import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem eq_exactImg_of_twin (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    {B : Subgroup (↥(exactLayer Ω (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(exactLayer Ω (u₁ * u₂)))}
    (hB : B ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)))
    (hzY : z ∈ exactLayer Ω (u₁ * u₂))
    (hzB : IsUniqueInvolution B (T7H.toBar Ω (u₁ * u₂) z hzY)) :
    B = T7H.exactImg Ω (u₁ * u₂) K₃ := by
  classical
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    isPGroup_zpowers_of_sq_eq_one h.sq_12
  obtain ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, hu₁R, hu₂R, hu₃R, c12, c13, c23, hj₁, hj₂, e₁, e₂,
    s₁, s₂⟩ := exists_invert h
  have d : InvData z u₁ u₂ j₁ j₂ R R' R₃ :=
    { z2 := h.hz.sq, s₁ := h.sq₁, s₂ := h.sq₂, u₁R := hu₁R, u₂R := hu₂R, j₁R := hj₁,
      j₂R := hj₂, c₁₂ := c12, c₁₃ := c13, c₂₃ := c23, inv₁ := e₁, inv₂ := e₂, sq₁ := s₁,
      sq₂ := s₂ }
  obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hB
  obtain ⟨w, hw⟩ : ∃ w, IsUniqueInvolution J w := by
    obtain ⟨w, hw⟩ := hΩ.classical J hJ.1
    exact ⟨w, ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hw⟩
  set Y : Subgroup G := exactLayer Ω (u₁ * u₂) with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hwc : w ∈ exactCore (u₁ * u₂) J := (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hJ hw).mem
  have hwY : w ∈ Y := exactCore_le_exactLayer hJ hwc
  have hB' := T7H.exactImg_isUnique hp hΩ hcpg hJ hw hwY
  have heq : T7H.toBar Ω (u₁ * u₂) w hwY = T7H.toBar Ω (u₁ * u₂) z hzY := hB'.eq hzB
  obtain ⟨n, hn, hnw⟩ := T3Core.exists_conj_of_map_eq_of_involutions hN₀odd
    (u := (⟨w, hwY⟩ : ↥Y)) (x := (⟨z, hzY⟩ : ↥Y)) (Subtype.ext hw.sq) (Subtype.ext h.hz.sq) heq
  have hnw' : (n : G) * w * (n : G)⁻¹ = z := congrArg Subtype.val hnw
  have hncent : (n : G) ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
    exactLayer_le_centralizer Ω (u₁ * u₂) n.2
  have hnc : (n : G) * (u₁ * u₂) * (n : G)⁻¹ = u₁ * u₂ := T7H.mem_centralizer_of_mem_exactLayer
  have hJ' : conjSub (n : G) J ∈ tqMembers Ω (u₁ * u₂) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hncent hJ
  have hzJ' : IsUniqueInvolution (conjSub (n : G) J) z := by
    have := hw.conj (n : G)
    rwa [hnw'] at this
  have hJ'V : conjSub (n : G) J ∈ twinSet Ω K := ⟨hJ'.1, z, h.hz, hzJ'⟩
  have hJ'K₃ : conjSub (n : G) J = K₃ := by
    rcases hV3 _ hJ'V with h1 | h1 | h1
    · exfalso
      have := hJ'.2
      rw [h1] at this
      exact not_mem_trivialOnQuot_left d h.hz (hR.1 hj₁) this
    · exfalso
      have := hJ'.2
      rw [h1] at this
      exact not_mem_trivialOnQuot_right d h.hzK' (hR'.1 hj₂) this
    · exact h1
  rw [← hJ'K₃]
  exact (T7H.exactImg_conjSub_odd hn hnc (K := J)).symm

end Twin

end S16

end CFSG.ClassicalInvolution.Asc77
