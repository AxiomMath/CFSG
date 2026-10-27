module

public import CFSG.ClassicalInvolution.Asc77.RLayerCentralizer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AXVPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ACaseBModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CaseB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
open CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

private theorem card_secQ_eq_card_A (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    Nat.card (SecQ R u) = Nat.card ((aeSub 5).map (mkQ 5)) := by
  classical
  obtain ⟨I⟩ := hA5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨J₁, J₂, x, κ₁, κ₂, vH, v', hJ₁, hJ₂, hne₂, hτ₁, hτ₂, hvx, hxx, hκ₁W, hκ₂W,
    hκ₁sq, hκ₂sq, hκ₁₂, hκ₁m, hκ₂m, hU₁, hU₂, hvH, hzv, hvHform, hvH2, hvHx, hvH1, hvHx1⟩ :=
    frame_at_u hc
  have hS := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.layer_q8Section hc.std.perp hd.hu2
  have hK₁ := secImg_mem_secFam hJ₁
  have hK₂ := secImg_mem_secFam hJ₂
  have hne : secImg (Om R) u J₂ ≠ secImg (Om R) u J₁ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.secImg_ne_of_twin hΩ hc2 hJ₂ hJ₁ hne₂ hτ₂ hτ₁
  have hker : I.φ.ker = ⊥ := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Q8.ae5_ker_bot hS I hK₁ hK₂ hne hU₁ hU₂
  have hgen : pSpan (TwinDisc.secFam (Om R) u) = ⊤ := TwinDisc.AE5.hgen_of hS
  have hcard : Nat.card ↥(pSpan (TwinDisc.secFam (Om R) u)) =
      Nat.card ((aeSub 5).map (mkQ 5)) := by
    have hprod := Subgroup.card_ker_mul_card_range I.φ
    rw [hker, Subgroup.card_bot, one_mul, I.range_eq] at hprod
    exact hprod.symm
  have htop : Nat.card (SecQ R u) =
      Nat.card ↥(pSpan (TwinDisc.secFam (Om R) u)) := by
    rw [hgen]
    exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
  rw [htop, hcard]

private theorem psi_range_eq (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    {ψ : SecQ R u →* AEQ 5} (hψinj : Function.Injective ψ)
    (hrange : (aeSub 5).map (mkQ 5) ≤ ψ.range) :
    ψ.range = (aeSub 5).map (mkQ 5) := by
  have hcard : Nat.card ψ.range = Nat.card (SecQ R u) := by
    have hprod := Subgroup.card_ker_mul_card_range ψ
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψinj, Subgroup.card_bot, one_mul] at hprod
    exact hprod
  refine (Subgroup.eq_of_le_of_card_ge hrange ?_).symm
  rw [hcard, card_secQ_eq_card_A hc hA5]

private theorem frame_psi_range (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    ∃ (x vH : ↥(coreHull (Om R) u)) (v' : Y)
      (ψ : SecQ R u →* AEQ 5) (p : Fin 5) (ι : Fin 4 ↪ Fin 5),
      hcoeHom (Om R) u x = u * e ∧ hcoeHom (Om R) u vH = v' ∧
      (t = v' ∨ t = u * v') ∧ Function.Injective ψ ∧
      ψ.range = (aeSub 5).map (mkQ 5) ∧
      ψ (QuotientGroup.mk x) = zBar (miss p) (card_miss p) ∧
      (∀ y, y ∈ Set.range ι ↔ y ≠ p) ∧
      ψ (QuotientGroup.mk vH) = mkQ 5 (embed ι w0) := by
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hxx, hvH, hzv, hvH2, hψinj, hrange, hψx, hι, hψv⟩ :=
    AY.frame_psi hc hA5
  exact ⟨x, vH, v', ψ, p, ι, hvx, hvH, hzv, hψinj, psi_range_eq hc hA5 hψinj hrange,
    hψx, hι, hψv⟩

private theorem oddCore_coreHull_u_eq_bot (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥ := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hOCu : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) = ⊥ := by
    have h := p23E8A_oddCoreIn_eq_bot hE hcit hP hc hA5 hαb
    rw [p23E8A_oddCoreIn_eq hc hA5 hαb] at h
    exact h
  exact AXV.hull_bot hΩ hc2u h2 (AXV.layer_bot hΩ hOCu)

private theorem mkQ_embed_w0_comm_zBar (p : Fin 5) (ι : Fin 4 ↪ Fin 5) :
    zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0) =
      mkQ 5 (embed ι w0) * zBar (miss p) (card_miss p) := by
  unfold zBar
  rw [← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, zOf_perm, embed_perm]
    simp only [w0, one_perm, embedPerm_one, Equiv.Perm.coe_one, id_eq]
    exact add_comm _ _
  · rw [mul_perm, mul_perm, zOf_perm, embed_perm]
    simp [w0]

private theorem commute_te_general {g v' e' : Y}
    (hu2 : u * u = 1) (hue : u * e' = e' * u) (hvu : v' * u = u * v')
    (hzv : t = v' ∨ t = u * v')
    (hg : Commute g (v' * (u * e'))) (hgu : Commute g u) :
    Commute g (t * e') := by
  have hmul : Commute g ((v' * (u * e')) * u) := hg.mul_right hgu
  rcases hzv with h | h
  · have hteu : (u * e') * u = e' := by
      calc (u * e') * u = u * (e' * u) := by group
        _ = u * (u * e') := by rw [hue]
        _ = (u * u) * e' := by group
        _ = e' := by rw [hu2, one_mul]
    have hte : t * e' = (v' * (u * e')) * u := by
      rw [h]
      calc v' * e' = v' * ((u * e') * u) := by rw [hteu]
        _ = (v' * (u * e')) * u := by group
    rw [hte]
    exact hmul
  · have hte : t * e' = v' * (u * e') := by
      rw [h]
      calc (u * v') * e' = (v' * u) * e' := by rw [hvu]
        _ = v' * (u * e') := by group
    rw [hte]
    exact hg

private noncomputable def layerSecEquiv
    (hmap : (coreHull (Om R) u).map (Subgroup.centralizer ({u} : Set Y)).subtype =
      rLayer (Om R) u)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥) :
    ↥(rLayer (Om R) u) ≃* SecQ R u :=
  (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv hmap).symm.trans
    (oddQuotientEquivOfCorefree hOu)

private theorem layerSecEquiv_hullEquiv_apply
    (hmap : (coreHull (Om R) u).map (Subgroup.centralizer ({u} : Set Y)).subtype =
      rLayer (Om R) u)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥)
    (z : ↥(coreHull (Om R) u)) :
    layerSecEquiv hmap hOu
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv hmap z) =
      (QuotientGroup.mk z : SecQ R u) := by
  rw [layerSecEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private structure CaseBFrameData (hc : P23Cfg n Y R S t K' W u e g) where
  hd : Hyp23bData (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W t u e g
  hΩ : HypOmegaGen (Om R)
  hmap : (coreHull (Om R) u).map (Subgroup.centralizer ({u} : Set Y)).subtype = rLayer (Om R) u
  hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥
  x : ↥(coreHull (Om R) u)
  vH : ↥(coreHull (Om R) u)
  v' : Y
  ψ : SecQ R u →* AEQ 5
  p : Fin 5
  ι : Fin 4 ↪ Fin 5
  hvx : hcoeHom (Om R) u x = u * e
  hvH : hcoeHom (Om R) u vH = v'
  hzv : t = v' ∨ t = u * v'
  hψinj : Function.Injective ψ
  hψrange : ψ.range = (aeSub 5).map (mkQ 5)
  hψx : ψ (QuotientGroup.mk x) = zBar (miss p) (card_miss p)
  hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p
  hψv : ψ (QuotientGroup.mk vH) = mkQ 5 (embed ι w0)
  e₀ : ↥(rLayer (Om R) u) ≃* SecQ R u
  he₀ : e₀ = layerSecEquiv hmap hOu
  Ψ : ↥(rLayer (Om R) u) →* AEQ 5
  hΨeq : Ψ = ψ.comp e₀.toMonoidHom
  hΨinj : Function.Injective Ψ
  hΨrange : Ψ.range = (aeSub 5).map (mkQ 5)

private structure CaseBFrameHull (hc : P23Cfg n Y R S t K' W u e g)
    extends CaseBFrameData hc where
  xY : ↥(rLayer (Om R) u)
  vY : ↥(rLayer (Om R) u)
  aY : ↥(rLayer (Om R) u)
  hxY : (xY : Y) = u * e
  hvY : (vY : Y) = toCaseBFrameData.v'
  haY : (aY : Y) = toCaseBFrameData.v' * (u * e)
  hΨx : toCaseBFrameData.Ψ xY = zBar (miss toCaseBFrameData.p) (card_miss toCaseBFrameData.p)
  hΨv : toCaseBFrameData.Ψ vY = mkQ 5 (embed toCaseBFrameData.ι w0)
  hΨa : toCaseBFrameData.Ψ aY =
    zBar (miss toCaseBFrameData.p) (card_miss toCaseBFrameData.p) *
      mkQ 5 (embed toCaseBFrameData.ι w0)
  hvu : toCaseBFrameData.v' * u = u * toCaseBFrameData.v'
  hue : u * e = e * u
  hut : u * t = t * u

private structure CaseBFrame (hc : P23Cfg n Y R S t K' W u e g) (y : Y)
    (hyY : y ∈ rLayer (Om R) u) extends CaseBFrameHull hc where
  s : AEQ 5
  hsdef : s = toCaseBFrameHull.toCaseBFrameData.Ψ ⟨y, hyY⟩
  hs : s ∈ (aeSub 5).map (mkQ 5)
  hs3 : IsPGroup 3 (Subgroup.zpowers s)
  hs1 : s ≠ 1
  hsb : s * mkQ 5 (embed toCaseBFrameHull.toCaseBFrameData.ι w0) =
    mkQ 5 (embed toCaseBFrameHull.toCaseBFrameData.ι w0) * s
  hyu : y * u = u * y
  hyv : y * toCaseBFrameHull.toCaseBFrameData.v' = toCaseBFrameHull.toCaseBFrameData.v' * y
  hyvY : (⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * toCaseBFrameHull.vY =
    toCaseBFrameHull.vY * ⟨y, hyY⟩
  hyte : y * (t * e) * y⁻¹ = t * (y * e * y⁻¹)

private theorem exists_caseBFrameData (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    Nonempty (CaseBFrameData hc) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hmap := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.coreHull_map_eq_rLayer
    hΩ hc2u h2
  have hOu := oddCore_coreHull_u_eq_bot hE hcit hP hc hA5 hαb
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hvH, hzv, hψinj, hψrange, hψx, hι, hψv⟩ :=
    frame_psi_range hc hA5
  let e₀ : ↥(rLayer (Om R) u) ≃* SecQ R u := layerSecEquiv hmap hOu
  let Ψ : ↥(rLayer (Om R) u) →* AEQ 5 := ψ.comp e₀.toMonoidHom
  have hΨinj : Function.Injective Ψ := hψinj.comp e₀.injective
  have hΨrange : Ψ.range = (aeSub 5).map (mkQ 5) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e₀.surjective, Subgroup.map_top,
      hψrange]
  exact ⟨{ hd := hd, hΩ := hΩ, hmap := hmap, hOu := hOu, x := x, vH := vH, v' := v',
           ψ := ψ, p := p, ι := ι, hvx := hvx, hvH := hvH, hzv := hzv, hψinj := hψinj,
           hψrange := hψrange, hψx := hψx, hι := hι, hψv := hψv, e₀ := e₀, he₀ := rfl,
           Ψ := Ψ, hΨeq := rfl, hΨinj := hΨinj, hΨrange := hΨrange }⟩

private theorem exists_caseBFrameHull (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    Nonempty (CaseBFrameHull hc) := by
  classical
  let D : CaseBFrameData hc := Classical.choice (exists_caseBFrameData hE hcit hP hc hA5 hαb)
  let xY : ↥(rLayer (Om R) u) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap D.x
  let vY : ↥(rLayer (Om R) u) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap D.vH
  let aY : ↥(rLayer (Om R) u) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap (D.vH * D.x)
  have hxY : (xY : Y) = u * e := by
    show hcoeHom (Om R) u D.x = u * e
    exact D.hvx
  have hvY : (vY : Y) = D.v' := by
    show hcoeHom (Om R) u D.vH = D.v'
    exact D.hvH
  have haY : (aY : Y) = D.v' * (u * e) := by
    show hcoeHom (Om R) u (D.vH * D.x) = D.v' * (u * e)
    rw [map_mul, D.hvH, D.hvx]
  have hΨx : D.Ψ xY = zBar (miss D.p) (card_miss D.p) := by
    rw [D.hΨeq]
    show D.ψ (D.e₀ xY) = _
    rw [D.he₀]
    change D.ψ (layerSecEquiv D.hmap D.hOu (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap D.x)) = _
    rw [layerSecEquiv_hullEquiv_apply D.hmap D.hOu D.x]
    exact D.hψx
  have hΨv : D.Ψ vY = mkQ 5 (embed D.ι w0) := by
    rw [D.hΨeq]
    show D.ψ (D.e₀ vY) = _
    rw [D.he₀]
    change D.ψ (layerSecEquiv D.hmap D.hOu (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap D.vH)) = _
    rw [layerSecEquiv_hullEquiv_apply D.hmap D.hOu D.vH]
    exact D.hψv
  have hΨa : D.Ψ aY = zBar (miss D.p) (card_miss D.p) * mkQ 5 (embed D.ι w0) := by
    rw [D.hΨeq]
    show D.ψ (D.e₀ aY) = _
    rw [D.he₀]
    change D.ψ (layerSecEquiv D.hmap D.hOu (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.hullEquiv D.hmap (D.vH * D.x))) = _
    rw [layerSecEquiv_hullEquiv_apply D.hmap D.hOu (D.vH * D.x)]
    rw [QuotientGroup.mk_mul, map_mul, D.hψv, D.hψx]
    exact (mkQ_embed_w0_comm_zBar D.p D.ι).symm
  have hvu : D.v' * u = u * D.v' := by
    have h := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam.hcoeHom_mem_centralizer
      (Om R) u D.vH
    rw [D.hvH] at h
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  have hue : u * e = e * u := by
    have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
      Q3CL.Thompson.commutes_of_mem_WSet D.hΩ D.hd.hW
    exact hWab _ D.hd.huW _ (T7K.e_mem_inf D.hd).1
  have hut : u * t = t * u := by
    have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
      Q3CL.Thompson.commutes_of_mem_WSet D.hΩ D.hd.hW
    exact hWab _ D.hd.huW _ D.hd.hzW
  exact ⟨{ toCaseBFrameData := D, xY := xY, vY := vY, aY := aY, hxY := hxY, hvY := hvY,
           haY := haY, hΨx := hΨx, hΨv := hΨv, hΨa := hΨa, hvu := hvu, hue := hue,
           hut := hut }⟩

private theorem exists_caseBFrame (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    {y : Y} (hyY : y ∈ rLayer (Om R) u) (hyt : y * t = t * y)
    (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hye : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹) :
    Nonempty (CaseBFrame hc y hyY) := by
  classical
  let H : CaseBFrameHull hc := Classical.choice (exists_caseBFrameHull hE hcit hP hc hA5 hαb)
  have hd := H.hd
  have hyu : y * u = u * y :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.rLayer_le_centralizer
        (Om R) u hyY)
  have hyv : y * H.v' = H.v' * y := by
    rcases H.hzv with h | h
    · rw [← h]; exact hyt
    · have huv : u * u = 1 := hd.hu2
      have hv' : H.v' = u * t := by
        calc H.v' = (u * u) * H.v' := by rw [huv, one_mul]
          _ = u * (u * H.v') := by group
          _ = u * t := by rw [← h]
      rw [hv']
      calc y * (u * t) = (y * u) * t := by group
        _ = (u * y) * t := by rw [hyu]
        _ = u * (y * t) := by group
        _ = u * (t * y) := by rw [hyt]
        _ = (u * t) * y := by group
  let s : AEQ 5 := H.Ψ ⟨y, hyY⟩
  have hs : s ∈ (aeSub 5).map (mkQ 5) := by
    have : s ∈ H.Ψ.range := ⟨⟨y, hyY⟩, rfl⟩
    rwa [H.hΨrange] at this
  have hy3' : IsPGroup 3 (Subgroup.zpowers (⟨y, hyY⟩ : ↥(rLayer (Om R) u))) := by
    have hcomap : (Subgroup.zpowers y).comap (Subgroup.subtype (rLayer (Om R) u)) =
        Subgroup.zpowers (⟨y, hyY⟩ : ↥(rLayer (Om R) u)) := by
      ext z
      rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨m, hm⟩
        exact ⟨m, Subtype.ext (by simpa using hm)⟩
      · rintro ⟨m, hm⟩
        exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    rw [← hcomap]
    exact hy3.comap_of_injective (Subgroup.subtype _) Subtype.val_injective
  have hs3 : IsPGroup 3 (Subgroup.zpowers s) := by
    rw [show s = H.Ψ ⟨y, hyY⟩ from rfl, ← MonoidHom.map_zpowers H.Ψ ⟨y, hyY⟩]
    exact hy3'.map H.Ψ
  have hs1 : s ≠ 1 := by
    have hy1 : y ≠ 1 := by
      intro h
      exact hye 1 (Subgroup.one_mem _) (by rw [h])
    intro h
    apply hy1
    have h1 : (⟨y, hyY⟩ : ↥(rLayer (Om R) u)) = 1 :=
      H.hΨinj (by rw [show H.Ψ ⟨y, hyY⟩ = s from rfl, h, map_one])
    exact congrArg Subtype.val h1
  have hyvY : (⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * H.vY = H.vY * ⟨y, hyY⟩ :=
    Subtype.ext (by simpa [H.hvY] using hyv)
  have hsb : s * mkQ 5 (embed H.ι w0) = mkQ 5 (embed H.ι w0) * s := by
    calc s * mkQ 5 (embed H.ι w0) = H.Ψ ⟨y, hyY⟩ * H.Ψ H.vY := by rw [H.hΨv]
      _ = H.Ψ ((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * H.vY) := by rw [map_mul]
      _ = H.Ψ (H.vY * ⟨y, hyY⟩) := by rw [hyvY]
      _ = H.Ψ H.vY * H.Ψ ⟨y, hyY⟩ := by rw [map_mul]
      _ = mkQ 5 (embed H.ι w0) * s := by rw [H.hΨv]
  have hyte : y * (t * e) * y⁻¹ = t * (y * e * y⁻¹) := by
    calc y * (t * e) * y⁻¹ = (y * t * y⁻¹) * (y * e * y⁻¹) := by group
      _ = t * (y * e * y⁻¹) := by rw [hyt]; group
  exact ⟨{ toCaseBFrameHull := H, s := s, hsdef := rfl, hs := hs, hs3 := hs3, hs1 := hs1,
           hsb := hsb, hyu := hyu, hyv := hyv, hyvY := hyvY, hyte := hyte }⟩

private theorem caseB_G₁_map {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY) :
    (Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u))).map F.Ψ =
      Subgroup.centralizer ({zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0)} :
        Set (AEQ 5)) ⊓ (aeSub 5).map (mkQ 5) := by
  rw [CFSG.Walter.JT.map_centralizer_singleton_of_injective F.Ψ F.hΨinj, F.hΨa,
    F.hΨrange, inf_comm]

private theorem caseB_G₂_map {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY) :
    (Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u))).map F.Ψ =
      Subgroup.centralizer ({F.s * (zBar (miss F.p) (card_miss F.p) *
        mkQ 5 (embed F.ι w0)) * F.s⁻¹} : Set (AEQ 5)) ⊓ (aeSub 5).map (mkQ 5) := by
  have hΨa' : F.Ψ ((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹) =
      F.s * (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0)) * F.s⁻¹ := by
    calc F.Ψ ((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
          (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹)
        = F.Ψ ⟨y, hyY⟩ * F.Ψ F.aY * (F.Ψ ⟨y, hyY⟩)⁻¹ := by simp only [map_mul, map_inv]
      _ = F.s * (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0)) * F.s⁻¹ := by
          rw [F.hΨa, F.hsdef]
  rw [CFSG.Walter.JT.map_centralizer_singleton_of_injective F.Ψ F.hΨinj, hΨa',
    F.hΨrange, inf_comm]

private theorem caseB_sup_centralizers {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY) :
    Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u)) ⊔
      Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
        (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u)) = ⊤ := by
  have hgen := caseB_model_gen F.p F.ι F.hι F.s F.hs F.hs3 F.hs1 F.hsb
  refine le_antisymm le_top ?_
  intro g hg
  have hgA : F.Ψ g ∈ (aeSub 5).map (mkQ 5) := F.hΨrange ▸ ⟨g, rfl⟩
  have hmem : F.Ψ g ∈
      (Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u))).map F.Ψ ⊔
      (Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
        (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u))).map F.Ψ := by
    have hthis := hgen.2 hgA
    rwa [← caseB_G₁_map F, ← caseB_G₂_map F] at hthis
  rw [← Subgroup.map_sup] at hmem
  obtain ⟨g', hg', hgg'⟩ := hmem
  rwa [F.hΨinj hgg'] at hg'

private theorem caseB_G₁_le_normalizer {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY) :
    Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u)) ≤
      (Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)).comap
        (Subgroup.subtype (rLayer (Om R) u)) := by
  intro g hg
  rw [Subgroup.mem_comap]
  have hga : Commute (g : Y) (F.aY : Y) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hgu : Commute (g : Y) u :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.rLayer_le_centralizer
        (Om R) u g.2)
  have hgte : (g : Y) * (t * e) = (t * e) * (g : Y) := by
    have hcomm : Commute (g : Y) (F.v' * (u * e)) := by rwa [← F.haY]
    exact commute_te_general (t := t) (u := u) F.hd.hu2 F.hue F.hvu F.hzv hcomm hgu
  exact mem_normalizer_iff_conjSub_eq.mpr
    (T8.rLayer_conjSub_eq F.hΩ.conjInvariant
      (Subgroup.mem_centralizer_singleton_iff.mpr hgte))

private theorem caseB_G₂_le_normalizer {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY)
    (hB : ∀ x ∈ rLayer (Om R) (t * e),
      (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹))) :
    Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u)) ≤
      (Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)).comap
        (Subgroup.subtype (rLayer (Om R) u)) := by
  have haY' : (((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ : ↥(rLayer (Om R) u)) : Y) =
      F.v' * (u * (y * e * y⁻¹)) := by
    show (y * (F.aY : Y) * y⁻¹) = _
    rw [F.haY]
    have hconj : y * (F.v' * (u * e)) * y⁻¹ =
        (y * F.v' * y⁻¹) * (y * u * y⁻¹) * (y * e * y⁻¹) := by group
    rw [hconj]
    have h1 : y * F.v' * y⁻¹ = F.v' := by rw [F.hyv]; group
    have h2 : y * u * y⁻¹ = u := by rw [F.hyu]; group
    rw [h1, h2]
    group
  have hcomm_uy : Commute u y := F.hyu.symm
  have hcomm_ue : Commute u e := F.hue
  have hue' : u * (y * e * y⁻¹) = (y * e * y⁻¹) * u :=
    ((hcomm_uy.mul_right hcomm_ue).mul_right hcomm_uy.inv_right).eq
  have hB' : rLayer (Om R) (t * e) ≤
      Subgroup.centralizer ({y * (t * e) * y⁻¹} : Set Y) := by
    rw [F.hyte]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hB z hz).symm
  have hL' : rLayer (Om R) (t * (y * e * y⁻¹)) = rLayer (Om R) (t * e) := by
    have h := CFSG.ClassicalInvolution.Asc77.rLayer_conj_eq_of_le_centralizer
      F.hΩ.conjInvariant hB'
    rwa [F.hyte] at h
  intro g hg
  rw [Subgroup.mem_comap]
  have hga : Commute (g : Y) (((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ : ↥(rLayer (Om R) u)) : Y) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hgu : Commute (g : Y) u :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.rLayer_le_centralizer
        (Om R) u g.2)
  have hgte' : Commute (g : Y) (t * (y * e * y⁻¹)) := by
    have hcomm : Commute (g : Y) (F.v' * (u * (y * e * y⁻¹))) := by rwa [← haY']
    exact commute_te_general (t := t) (u := u) F.hd.hu2 hue' F.hvu F.hzv hcomm hgu
  have h := T8.rLayer_conjSub_eq F.hΩ.conjInvariant
    (a := t * (y * e * y⁻¹))
    (Subgroup.mem_centralizer_singleton_iff.mpr hgte')
  rw [hL'] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

theorem rLayer_u_le_normalizer (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    {y : Y} (hyY : y ∈ rLayer (Om R) u) (hyt : y * t = t * y)
    (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hye : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹)
    (hB : ∀ x ∈ rLayer (Om R) (t * e), (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹))) :
    rLayer (Om R) u ≤ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y) := by
  classical
  let F : CaseBFrame hc y hyY :=
    Classical.choice (exists_caseBFrame hE hcit hP hc hA5 hαb hyY hyt hy3 hye)
  let N₀ : Subgroup ↥(rLayer (Om R) u) :=
    (Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)).comap
      (Subgroup.subtype (rLayer (Om R) u))
  have hsup : Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u)) ⊔
      Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
        (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u)) = ⊤ :=
    caseB_sup_centralizers F
  have hG₁N : Subgroup.centralizer ({F.aY} : Set ↥(rLayer (Om R) u)) ≤ N₀ :=
    caseB_G₁_le_normalizer F
  have hG₂N : Subgroup.centralizer ({(⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹} : Set ↥(rLayer (Om R) u)) ≤ N₀ :=
    caseB_G₂_le_normalizer F hB
  intro g hg
  have htop : (⊤ : Subgroup ↥(rLayer (Om R) u)) ≤ N₀ := by
    rw [← hsup]
    exact sup_le hG₁N hG₂N
  exact Subgroup.mem_comap.mp (htop (Subgroup.mem_top (⟨g, hg⟩ : ↥(rLayer (Om R) u))))

private theorem caseB_cY_eq {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY) :
    (((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ * F.aY⁻¹ : ↥(rLayer (Om R) u)) : Y) =
      y * (t * e) * y⁻¹ * (t * e)⁻¹ := by
  show y * (F.aY : Y) * y⁻¹ * (F.aY : Y)⁻¹ = _
  have hux : u * (t * e) = (t * e) * u := by
    calc u * (t * e) = (u * t) * e := by group
      _ = (t * u) * e := by rw [F.hut]
      _ = t * (u * e) := by group
      _ = t * (e * u) := by rw [F.hue]
      _ = (t * e) * u := by group
  rcases F.hzv with h | h
  · have haY1 : (F.aY : Y) = u * (t * e) := by
      calc (F.aY : Y) = F.v' * (u * e) := F.haY
        _ = t * (u * e) := by rw [← h]
        _ = (t * u) * e := by group
        _ = (u * t) * e := by rw [F.hut]
        _ = u * (t * e) := by group
    rw [haY1, hux]
    simpa only [commutatorElement_def] using
      CFSG.ClassicalInvolution.ModelFacts.TG3.commutatorElement_mul_of_commute (y := t * e) F.hyu
  · have haY2 : (F.aY : Y) = t * e := by
      calc (F.aY : Y) = F.v' * (u * e) := F.haY
        _ = (F.v' * u) * e := by group
        _ = (u * F.v') * e := by rw [F.hvu]
        _ = t * e := by rw [← h]
    rw [haY2]

private theorem caseB_cY_mem_centralizer {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY)
    (hB : ∀ x ∈ rLayer (Om R) (t * e),
      (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹))) :
    (((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
      (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ * F.aY⁻¹ : ↥(rLayer (Om R) u)) : Y) ∈
      Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  rw [caseB_cY_eq F]
  have hcomm1 : Commute l (y * (t * e) * y⁻¹) := by
    have h := hB l hl
    rw [← F.hyte] at h
    exact h.symm
  have hcomm2 : Commute l (t * e) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.rLayer_le_centralizer
        (Om R) (t * e) hl)
  exact (hcomm1.mul_right hcomm2.inv_right).eq

private theorem caseB_N₀_normal {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY)
    (hN : rLayer (Om R) u ≤ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)) :
    rLayer (Om R) u ≤ Subgroup.normalizer
      ((Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y) ⊓ rLayer (Om R) u :
        Subgroup Y) : Set Y) := by
  have hstep : ∀ g ∈ rLayer (Om R) u, ∀ m,
      m ∈ Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y) ⊓ rLayer (Om R) u →
      g * m * g⁻¹ ∈
        Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y) ⊓ rLayer (Om R) u := by
    intro g hg m hm
    have hgN : g ∈ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y) := hN hg
    have hginv : g⁻¹ ∈ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y) :=
      (Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)).inv_mem hgN
    refine ⟨?_, ?_⟩
    · change g * m * g⁻¹ ∈ Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hgl : g⁻¹ * l * g ∈ rLayer (Om R) (t * e) := by
        simpa using (Subgroup.mem_normalizer_iff.mp hginv l).mp hl
      have hmc := Subgroup.mem_centralizer_iff.mp hm.1 (g⁻¹ * l * g) hgl
      have hconj : (g * m * g⁻¹) * l * (g * m * g⁻¹)⁻¹ = l := by
        calc (g * m * g⁻¹) * l * (g * m * g⁻¹)⁻¹
            = g * (m * (g⁻¹ * l * g)) * m⁻¹ * g⁻¹ := by group
          _ = g * ((g⁻¹ * l * g) * m) * m⁻¹ * g⁻¹ := by rw [← hmc]
          _ = g * (g⁻¹ * l * g) * g⁻¹ := by group
          _ = l := by group
      calc l * (g * m * g⁻¹)
          = ((g * m * g⁻¹) * l * (g * m * g⁻¹)⁻¹) * (g * m * g⁻¹) := by rw [hconj]
        _ = (g * m * g⁻¹) * l := by group
    · have hgC : g ∈ Subgroup.centralizer ({u} : Set Y) :=
        CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.rLayer_le_centralizer
          (Om R) u hg
      have hgNr : g ∈ Subgroup.normalizer (rLayer (Om R) u : Set Y) :=
        mem_normalizer_iff_conjSub_eq.mpr (T8.rLayer_conjSub_eq F.hΩ.conjInvariant hgC)
      exact (Subgroup.mem_normalizer_iff.mp hgNr m).mp hm.2
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro m
  exact ⟨hstep g hg m, fun hm => by
    have h := hstep g⁻¹ ((rLayer (Om R) u).inv_mem hg) (g * m * g⁻¹) hm
    rwa [show g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m from by group] at h⟩

private theorem caseB_model_normal_step {hc : P23Cfg n Y R S t K' W u e g} {y : Y} {hyY : y ∈ rLayer (Om R) u}
    (F : CaseBFrame hc y hyY)
    (hB : ∀ x ∈ rLayer (Om R) (t * e),
      (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹)))
    (hN : rLayer (Om R) u ≤ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)) :
    zBar (miss F.p) (card_miss F.p) ∈
      (((Subgroup.centralizer (rLayer (Om R) (t * e) : Set Y) ⊓
        rLayer (Om R) u).subgroupOf (rLayer (Om R) u)).map F.Ψ) := by
  let L : Subgroup Y := rLayer (Om R) (t * e)
  let N₀ : Subgroup Y := Subgroup.centralizer (L : Set Y) ⊓ rLayer (Om R) u
  let N₁ : Subgroup ↥(rLayer (Om R) u) := N₀.subgroupOf (rLayer (Om R) u)
  have hN₁_normal : N₁.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show N₀ ≤ rLayer (Om R) u from inf_le_right)).mpr (caseB_N₀_normal F hN)
  let N_A : Subgroup (AEQ 5) := N₁.map F.Ψ
  have hNA : N_A ≤ (aeSub 5).map (mkQ 5) := by
    intro m hm
    obtain ⟨n, -, rfl⟩ := hm
    exact F.hΨrange ▸ ⟨n, rfl⟩
  have hNn : ∀ x ∈ (aeSub 5).map (mkQ 5), ∀ m ∈ N_A, x * m * x⁻¹ ∈ N_A := by
    intro x hx m hm
    rw [← F.hΨrange] at hx
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨n, hn, rfl⟩ := hm
    have hmem : h * n * h⁻¹ ∈ N₁ := hN₁_normal.conj_mem n hn h
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem F.Ψ hmem
  let cY : ↥(rLayer (Om R) u) :=
    (⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY * (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ * F.aY⁻¹
  have hcY_N₁ : cY ∈ N₁ := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨caseB_cY_mem_centralizer F hB, cY.2⟩
  have hcomm_mem : F.s * (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0)) * F.s⁻¹ *
      (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0))⁻¹ ∈ N_A := by
    have hmapc : F.Ψ cY = F.s * (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0)) *
        F.s⁻¹ * (zBar (miss F.p) (card_miss F.p) * mkQ 5 (embed F.ι w0))⁻¹ := by
      show F.Ψ ((⟨y, hyY⟩ : ↥(rLayer (Om R) u)) * F.aY *
        (⟨y, hyY⟩ : ↥(rLayer (Om R) u))⁻¹ * F.aY⁻¹) = _
      simp only [map_mul, map_inv]
      rw [F.hΨa, F.hsdef]
    rw [← hmapc]
    exact Subgroup.mem_map_of_mem F.Ψ hcY_N₁
  exact caseB_model_normal F.p F.ι F.hι F.s F.hs F.hs3 F.hs1 F.hsb N_A hNA hNn hcomm_mem

theorem rLayer_te_le_centralizer_ue (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    {y : Y} (hyY : y ∈ rLayer (Om R) u) (hyt : y * t = t * y)
    (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hye : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹)
    (hB : ∀ x ∈ rLayer (Om R) (t * e), (t * (y * e * y⁻¹)) * x = x * (t * (y * e * y⁻¹)))
    (hN : rLayer (Om R) u ≤ Subgroup.normalizer (rLayer (Om R) (t * e) : Set Y)) :
    rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({u * e} : Set Y) := by
  classical
  let F : CaseBFrame hc y hyY :=
    Classical.choice (exists_caseBFrame hE hcit hP hc hA5 hαb hyY hyt hy3 hye)
  let L : Subgroup Y := rLayer (Om R) (t * e)
  let N₀ : Subgroup Y := Subgroup.centralizer (L : Set Y) ⊓ rLayer (Om R) u
  let N₁ : Subgroup ↥(rLayer (Om R) u) := N₀.subgroupOf (rLayer (Om R) u)
  let N_A : Subgroup (AEQ 5) := N₁.map F.Ψ
  have hzbar : zBar (miss F.p) (card_miss F.p) ∈ N_A :=
    caseB_model_normal_step F hB hN
  obtain ⟨n, hn, hΨn⟩ := hzbar
  have hnx : n = F.xY := F.hΨinj (hΨn.trans F.hΨx.symm)
  have hxY_N₁ : F.xY ∈ N₁ := by rwa [← hnx]
  have hxY_N₀ : (F.xY : Y) ∈ N₀ := by
    rwa [Subgroup.mem_subgroupOf] at hxY_N₁
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  simpa [F.hxY] using Subgroup.mem_centralizer_iff.mp hxY_N₀.1 l hl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CaseB
