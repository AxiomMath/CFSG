module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOCard
import CFSG.ClassicalInvolution.Asc77.RLayerCentralizer
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf25Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.TC.Thin

theorem card_sec_eq_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (φ : A ≃* B) :
    Nat.card (A ⧸ classicalInvolutionOddCore A) = Nat.card (B ⧸ classicalInvolutionOddCore B) :=
  Nat.card_congr
    (QuotientGroup.congr _ _ φ (TwinPerpV3.classicalInvolutionOddCore_map_equiv φ)).toEquiv

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem card_secQ_conj (hc : P23Cfg n Y R S t K' W u e g) {f : Y} (hf : f * f = 1) (m : Y) :
    Nat.card (SecQ R (m * f * m⁻¹)) = Nat.card (SecQ R f) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hf2 : IsPGroup 2 (Subgroup.zpowers f) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf
  have hg2 : IsPGroup 2 (Subgroup.zpowers (m * f * m⁻¹)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one (by
      calc m * f * m⁻¹ * (m * f * m⁻¹) = m * (f * f) * m⁻¹ := by group
        _ = 1 := by rw [hf]; group)
  have hmf := TwinPerpV3.coreHull_map_eq_rLayer hΩ hf2 h2
  have hmg := TwinPerpV3.coreHull_map_eq_rLayer hΩ hg2 h2
  have hlay : (rLayer (Om R) f).map (MulAut.conj m).toMonoidHom = rLayer (Om R) (m * f * m⁻¹) :=
    (CFSG.ClassicalInvolution.Asc77.rLayer_conj (CFSG.ClassicalInvolution.Asc77.conjInvariant_conjClass
      (tightCore R)) m f).symm
  let φ : ↥(rLayer (Om R) f) ≃* ↥(rLayer (Om R) (m * f * m⁻¹)) :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).trans
      (MulEquiv.subgroupCongr hlay)
  calc Nat.card (SecQ R (m * f * m⁻¹))
      = Nat.card (↥(rLayer (Om R) (m * f * m⁻¹)) ⧸
          classicalInvolutionOddCore ↥(rLayer (Om R) (m * f * m⁻¹))) :=
        Nat.card_congr (TwinPerpV3.secEquiv hmg).toEquiv
    _ = Nat.card (↥(rLayer (Om R) f) ⧸ classicalInvolutionOddCore ↥(rLayer (Om R) f)) :=
        (card_sec_eq_of_mulEquiv φ).symm
    _ = Nat.card (SecQ R f) := (Nat.card_congr (TwinPerpV3.secEquiv hmf).toEquiv).symm

theorem not_conj_e_u (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) (hA6 : SecAE R e 6) (h : Y) :
    e ≠ h * u * h⁻¹ := by
  intro heq
  have hd := hc.data
  have hcard : Nat.card (SecQ R e) = Nat.card (SecQ R u) := by
    rw [heq]
    exact card_secQ_conj hc hd.hu2 h
  obtain ⟨x, vH, v', ψ, p, ι, -, -, -, -, -, hψinj, -⟩ := AY.frame_psi hc hA5
  have h5 : Nat.card (SecQ R u) ≤ 3840 :=
    (Nat.card_le_card_of_injective ψ hψinj).trans card_AEQ_five_le
  have h6 : 5760 ≤ Nat.card (SecQ R e) := by
    obtain ⟨I⟩ := hA6
    have h1 : Nat.card ↥I.φ.range ≤ Nat.card ↥(pSpan (TwinDisc.secFam (Om R) e)) :=
      Nat.card_le_card_of_surjective I.φ.rangeRestrict I.φ.rangeRestrict_surjective
    have h2 : Nat.card ↥(pSpan (TwinDisc.secFam (Om R) e)) ≤ Nat.card (SecQ R e) :=
      Subgroup.card_le_card_group _
    have h3 : Nat.card ↥I.φ.range = Nat.card ↥((aeSub 6).map (mkQ 6)) := by rw [I.range_eq]
    have h4 := five_thousand_le_card_ae6
    omega
  omega

theorem not_conj_e_te (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) (hA6 : SecAE R e 6) (k : Y) :
    e ≠ k * (t * e) * k⁻¹ := by
  intro hk
  have hd := hc.data
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hge : g * e * g⁻¹ = e := by
    rw [T7K.comm_e hd hgN]
    group
  have hgze : g * (t * e) * g⁻¹ = u := by
    calc g * (t * e) * g⁻¹ = (g * t * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hd.hgt, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2, mul_one]
  apply not_conj_e_u hc hA5 hA6 (k * g⁻¹)
  calc e = k * (t * e) * k⁻¹ := hk
    _ = k * g⁻¹ * (g * (t * e) * g⁻¹) * g * k⁻¹ := by group
    _ = k * g⁻¹ * u * g * k⁻¹ := by rw [hgze]
    _ = (k * g⁻¹) * u * (k * g⁻¹)⁻¹ := by group

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
