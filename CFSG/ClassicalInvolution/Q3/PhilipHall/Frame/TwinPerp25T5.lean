module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3E

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Layer

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem nc4_not_weak (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) :
    ¬ NC4Weak (TwinDisc.secFam Ω a) := by
  rintro ⟨M₁, hM₁, y, hyM₁, hy4o, M₂, hM₂, s₂, hs₂, hne, hcomm⟩
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hy4 : y * y * y * y = 1 := by
    have h : y ^ 4 = 1 := hy4o ▸ pow_orderOf_eq_one y
    simpa [pow_succ, mul_assoc] using h
  have hy2 : y * y ≠ 1 := by
    intro h
    have h' : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hy4o] at h'
    omega
  obtain ⟨N₂, hN₂, rfl⟩ := exists_of_mem_secFam hM₂
  obtain ⟨g₂, hg₂⟩ := hyp.std.1.stand.trans N₂ hN₂.1
  have hzN₂ : IsUniqueInvolution N₂ (g₂ * z * g₂⁻¹) := by
    rw [← hg₂]
    exact hyp.std.setting.hz.conj g₂
  obtain ⟨hbC, hbY, hbb⟩ := isUniqueInvolution_secImg hΩ hc2 hN₂ hzN₂
  have hz₂b : s₂ = QuotientGroup.mk (⟨⟨g₂ * z * g₂⁻¹, hbC⟩, hbY⟩ : ↥(coreHull Ω a)) := hs₂.eq hbb
  have hfix : secAct hΩ hc2 ⟨g₂ * z * g₂⁻¹, hbC⟩ y = y := by
    rw [secAct_of_mem hΩ hc2 hbY, MulAut.conj_apply, ← hz₂b, hcomm, mul_assoc, mul_inv_cancel,
      mul_one]
  obtain ⟨w, hw, hwy⟩ := nc4_lift_sec2 hyp hΩ hc2 hbC hM₁ hyM₁ hy4 hy2 hfix
  have hweq : w = ⟨⟨g₂ * z * g₂⁻¹, hbC⟩, hbY⟩ := Subtype.ext (Subtype.ext hw)
  apply hne
  rw [hz₂b, ← hweq, hwy]

theorem layer_nbr (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hacA : a ∈ cA S R R') :
    secImg Ω a K' ∈ omegaNbr (TwinDisc.secFam Ω a) (secImg Ω a K) := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, hK'tq, hz, hz', -, -⟩ := layer_twins_tq hyp hacA
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hKΩ : K ∈ Ω := hyp.std.1.stand.mem
  have hK'Ω : K' ∈ Ω := hyp.std.1.hK'.1
  have hRK : IsSylow2In R K := h.hRsyl
  have hR'K' : IsSylow2In R' K' := h.hR'syl
  have hcommR : Commutes R R' := h.hcomm
  have hcommA : ∀ x ∈ R ⊔ R', x * a = a * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hacA.2 x hx
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommA x (Subgroup.mem_sup_left hx))
  have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommA x (Subgroup.mem_sup_right hx))
  have hR'N : R' ≤ Subgroup.normalizer (K : Set G) :=
    (Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hKΩ hyp.std.1.hne hz' hz).trans' hR'K'.1
  exact omegaNbr_secImg hΩ hc2 hKtq hK'tq hRK hR'K' hRc hR'c hcommR hR'N

theorem twinSecCtx_of_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply)
    (hOE : TwinDisc.OddCentEdge (Nat.card G)) (hbad : BadElt z a) :
    TwinSecCtx (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a))
      (TwinDisc.secFam Ω a) := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  have htr := layer_transitive_of_bad hyp ha2 ha1 hacA hT hbad
  have hedge := layer_edge hyp ha2 hacA
  have hodd := hOE hih.1 hih.2 _ hlt _ hS htr hedge
  obtain ⟨hKtq, hK'tq, hz, hz', hperp₁, hperp₂⟩ := layer_twins_tq hyp hacA
  obtain ⟨htC₁, htY₁, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
  have hmem := ExitU.members hS htr (secImg_mem_secFam hKtq) hz₁
    (hodd _ (secImg_mem_secFam hKtq) _ hz₁)
  refine ⟨hS, htr, fun J hJ => (hmem J hJ).1, fun J hJ => (hmem J hJ).2, ?_,
    nc4_not_weak hyp ha2, ?_⟩
  · refine ⟨secImg Ω a K, secImg_mem_secFam hKtq, secImg Ω a K', secImg_mem_secFam hK'tq,
      QuotientGroup.mk (⟨⟨z, htC₁⟩, htY₁⟩ : ↥(coreHull Ω a)), layer_nbr hyp ha2 hacA, hz₁, hz₂, ?_⟩
    intro M hM
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM.1
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hKtq hJ₀ hperp₁ hM
  · intro z' hall
    apply hbad
    have hz'eq : z' = QuotientGroup.mk (⟨⟨z, htC₁⟩, htY₁⟩ : ↥(coreHull Ω a)) :=
      (hall _ (secImg_mem_secFam hKtq)).eq hz₁
    refine TwinPerpV3.mem_zStarOf_of_allMembers hΩ hc2 hKtq htC₁ htY₁ ?_
    intro M hM
    have h1 := hall M hM
    rw [hz'eq] at h1
    exact h1

end Layer

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
