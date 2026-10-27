module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M7

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Twin

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_sq_of_order_four {J : Subgroup G} {w v : G} (hw : IsUniqueInvolution J w) (hv : v ∈ J)
    (hv4 : orderOf v = 4) : v * v = w := by
  have hv22 : (v * v) * (v * v) = 1 := by
    have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
    simpa [pow_succ, mul_assoc] using this
  rcases hw.unique (v * v) (J.mul_mem hv hv) hv22 with h | h
  · exfalso
    have h2 : v ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hv4] at this
    omega
  · exact h

theorem layer_mem_secImg (hΩ : HypOmegaGen Ω) {a : G} (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    {J P : Subgroup G} {u : G} (hJ : J ∈ tqMembers3 Ω a) (hP : IsSylow2In P J)
    (hPc : P ≤ Subgroup.centralizer ({a} : Set G)) (hu : u ∈ P) :
    ∃ (huC : u ∈ Subgroup.centralizer ({a} : Set G))
      (huY : (⟨u, huC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ coreHull Ω a),
      (QuotientGroup.mk (⟨⟨u, huC⟩, huY⟩ : ↥(coreHull Ω a)) :
          ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)) ∈ secImg Ω a J := by
  have hPs : IsSylow2In P (TwinADescent.coreAt a J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hP, hPc⟩
  have hu' : u ∈ TwinADescent.coreAt a J := hPs.1 hu
  have huC : u ∈ Subgroup.centralizer ({a} : Set G) := TwinADescent.coreAt_le_centralizer a J hu'
  have huY : (⟨u, huC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ coreHull Ω a :=
    le_coreHull hJ (Subgroup.mem_subgroupOf.mpr hu')
  exact ⟨huC, huY, Subgroup.mem_map.mpr ⟨⟨⟨u, huC⟩, huY⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hu'), rfl⟩⟩

theorem layer_twinSect0 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hno : SecNoExitAt Ω a) :
    ∃ (htC : z ∈ Subgroup.centralizer ({a} : Set G))
      (htY : (⟨z, htC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ coreHull Ω a)
      (A A' : Subgroup (↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)))
      (a₀ b₀ : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a)),
      TwinSect0 (liftFam (TwinDisc.secFam Ω a)) A A'
        (QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(coreHull Ω a))) a₀ b₀ := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, hK'tq, hz, hz', hperp₁, hperp₂⟩ := layer_twins_tq hyp hacA
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2', hl, hex⟩ := lifts_of_noExit hih.2 hlt hS hno
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
  obtain ⟨htC, htY, hzbar⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨htC', htY', hzbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
  have hJΦ : secImg Ω a K ∈ TwinDisc.secFam Ω a := secImg_mem_secFam hKtq
  have hJ'Φ : secImg Ω a K' ∈ TwinDisc.secFam Ω a := secImg_mem_secFam hK'tq
  obtain ⟨L, u₀, hL⟩ := hl _ hJΦ
  obtain ⟨L', u₀', hL'⟩ := hl _ hJ'Φ
  have hu₀ := hL.inv.eq hzbar
  have hu₀' := hL'.inv.eq hzbar'
  have hu₀₀ : u₀' = u₀ := hu₀'.trans hu₀.symm
  subst hu₀₀
  have hAmem := satU_mem_liftFam hJΦ hL
  have hBmem := satU_mem_liftFam hJ'Φ hL'
  have hxA : IsUniqueInvolution (satU (.sl2 3 1) L u₀') u₀' :=
    isUniqueInvolution_liftFam_of_le hAmem hL.inv hL.le_sat
  have hxB : IsUniqueInvolution (satU (.sl2 3 1) L' u₀') u₀' :=
    isUniqueInvolution_liftFam_of_le hBmem hL'.inv hL'.le_sat
  have hBnbr := (hex.mem_omegaNbr_liftFam_iff hS.hyp h2' hl hAmem hJΦ hL.le_sat hBmem hJ'Φ hL'.le_sat).mpr
      (omegaNbr_secImg hΩ hc2 hKtq hK'tq hRK hR'K' hRc hR'c hcommR hR'N)
  obtain ⟨hu₁C, hu₁Y, hu₁mem⟩ := layer_mem_secImg hΩ hc2 hKtq hRK hRc hyp.hu₁.1
  obtain ⟨hu₂C, hu₂Y, hu₂mem⟩ := layer_mem_secImg hΩ hc2 hK'tq hR'K' hR'c hyp.hu₂.1
  have hsq₁ : u₁ * u₁ = z := layer_sq_of_order_four hz (hRK.1 hyp.hu₁.1) hyp.hu₁.2.1
  have hsq₂ : u₂ * u₂ = z := layer_sq_of_order_four hz' (hR'K'.1 hyp.hu₂.1) hyp.hu₂.2.1
  refine ⟨htC, htY, satU (.sl2 3 1) L u₀', satU (.sl2 3 1) L' u₀',
    QuotientGroup.mk ⟨⟨u₁, hu₁C⟩, hu₁Y⟩, QuotientGroup.mk ⟨⟨u₂, hu₂C⟩, hu₂Y⟩, ?_⟩
  rw [← hu₀]
  refine ⟨hAmem, hBmem, hBnbr.2.1.symm, hxA, hxB, hL.le_sat hu₁mem, hL'.le_sat hu₂mem, ?_, ?_, ?_, ?_⟩
  · rw [hu₀, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subtype.ext hsq₁)
  · rw [hu₀, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subtype.ext hsq₂)
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, hJ₀M⟩ := exists_core_of_mem_liftFam hM
    obtain ⟨J₁, hJ₁tq, rfl⟩ := exists_of_mem_secFam hJ₀
    have hn := (hex.mem_omegaNbr_liftFam_iff hS.hyp h2' hl hAmem hJΦ hL.le_sat hM hJ₀ hJ₀M).mp hMn
    have heq := TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hKtq hJ₁tq hperp₁ hn
    exact liftFam_eq_of_le hS.hyp hM hBmem hJ₀ hJ₀M (by rw [heq]; exact hL'.le_sat)
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, hJ₀M⟩ := exists_core_of_mem_liftFam hM
    obtain ⟨J₁, hJ₁tq, rfl⟩ := exists_of_mem_secFam hJ₀
    have hn := (hex.mem_omegaNbr_liftFam_iff hS.hyp h2' hl hBmem hJ'Φ hL'.le_sat hM hJ₀ hJ₀M).mp hMn
    have heq := TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK'tq hJ₁tq hperp₂ hn
    exact liftFam_eq_of_le hS.hyp hM hAmem hJ₀ hJ₀M (by rw [heq]; exact hL.le_sat)

end Twin

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
