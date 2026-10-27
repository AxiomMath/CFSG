module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiInnerV
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Main
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Bound

theorem card_centralizer_conj_eq_twisted {M : Type*} [Group M] (g w : M) :
    Nat.card (centralizer ({w} : Set M)) = Nat.card (centralizer ({g * w * g⁻¹} : Set M)) := by
  have hmap : (centralizer ({w} : Set M)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * w * g⁻¹} : Set M) := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
        _ = g * (w * y) * g⁻¹ := by rw [hy]
        _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
        _ = w * (g⁻¹ * x * g) := by group
  rw [← hmap, card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]

theorem two_pow_dvd_card_centralizer_twistedE6 {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {w : graphFixedRootGroup TwistTag.E6 K σ} (hw : orderOf w = 2) :
    2 ^ (26 * f) ∣ Nat.card (centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := TwistedE6Pilot.finite_of_card hK
  have : CharP K 2 := TwistedE6Pilot.charP_two_of_card (by omega) hK
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨σE, rfl⟩ := TwistedE6Pilot.exists_ringEquiv_toRingHom_eq σ
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card (by omega) hk hK
  let _ : Algebra (GaloisField 2 f) K := ι.toAlgebra
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction (by omega) hK
    (fun c => hσ c) (twistedE6FrameReduction (by omega) hK (fun c => hσ c)) hw2 hw1
  rw [card_centralizer_conj_eq_twisted g w]
  rcases hg with h | h | h
  · have hs : g * w * g⁻¹ = TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK hσ) 0 :=
      Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega)).trans
      (TwistedE6Pilot.two_pow_dvd_card_centralizer_stdRepC_zero (by omega) hK hσ)
  · have hs : g * w * g⁻¹ = TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK hσ) 1 :=
      Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega)).trans
      (TwistedE6Pilot.two_pow_dvd_card_centralizer_stdRepC_one (k := GaloisField 2 f) hf hk hK hσ)
  · have hs : g * w * g⁻¹ = ⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (TwistedE6Pilot.apply_apply_eq hK hσ)⟩ :=
      Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega)).trans
      (two_pow_dvd_card_centralizer_twistedE6ClassV (k := GaloisField 2 f) hk hK hσ)

end Bound

section Step1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_twistedE6_row (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K₂ σ →* _).range := by
  have := TwistedE6Pilot.finite_of_card hK₂
  have : CharP K₂ 2 := TwistedE6Pilot.charP_two_of_card (by omega) hK₂
  rintro ⟨c, hc⟩
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := E6Pilot.eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := E6Pilot.normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨u, hu⟩ : ∃ u : graphFixedRootGroup TwistTag.E6 K₂ σ, orderOf u = 2 := by
        refine ⟨TwistedE6Pilot.stdRepC (TwistedE6Pilot.apply_apply_eq hK₂ hσ) 0,
          orderOf_eq_prime ?_ ?_⟩
        · exact Subtype.ext (TwistedE6Pilot.stdRep_sq 0)
        · intro h1
          have h2 := congrArg (fun z : graphFixedRootGroup TwistTag.E6 K₂ σ =>
            (z : ModGL TwistTag.E6.tag K₂)) h1
          exact CFSG.LieType.Chevalley.E6SecondGraphFixed.pinnedX_e6HighestRoot_one_ne_one h2
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [E6Pilot.mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := E6Pilot.odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : graphFixedRootGroup TwistTag.E6 K₂ σ := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set (graphFixedRootGroup TwistTag.E6 K₂ σ)) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := E6Pilot.exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [E6Pilot.mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  have hdvd : 2 ^ (26 * f) ∣ Nat.card (centralizer ({t} : Set G)) := by
    refine (two_pow_dvd_card_centralizer_twistedE6 hf hK₂ hσ hŵ).trans ?_
    refine (card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [← card_map_of_injective M.subtype_injective]
    exact card_dvd_of_le hleG
  exact not_two_pow_dvd_card_centralizer_F4 hset hf hK e htC ht hKt hdvd

end Step1

section Input

theorem twistedE6RowInnerInput_holds : TwistedE6RowInnerInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ K' _ _ σ' hK' hσ' he₆ _ M hM htM eM
  obtain ⟨e₀⟩ := he₆
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
  have hLG₀ := le_pieceSpan hq e
  have h36 : 2 ^ (36 * f) ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K' σ'.toRingHom) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two (by omega) hK'
      σ'.toRingHom hσ']
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordTwistedE6' (by omega : 1 ≤ f)).two
    rw [hr, mul_comm 36 f]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (pieceSpan e : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e
      hw.mem_centralizer hw.orderOf_eq hG₀ e₀ h36
  have hZ := odd_card_center_of_odd_card_centralizer
    (odd_card_centralizer_pieceSpan hw e hLG₀ htC)
  obtain ⟨g, rfl⟩ := hM
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  exact not_inner_quot_twistedE6_row hw.standard hf hw.card_eq e hw.mem_centralizer
    hw.orderOf_eq hw.inf_eq hMp hZM hK' (fun c => hσ' c) eM htM

end Input

section Main

theorem seitzExclusion_highF4_of_xiInputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hSp6Odd : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual)
    (hGr : GraphPieceTablesInput) (hECT : E6RowCTQuotInput) (hEξ : E6RowXiExclusionInput)
    (hTCT : TwistedE6RowCTQuotInput) (hTξ : TwistedE6RowXiExclusionInput) (h2 : TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_xiInputs hGLS hSp6Odd hMinn hMcomp hres hGr hECT hEξ hTCT
    twistedE6RowInnerInput_holds hTξ h2

end Main

end CFSG.SeitzReduction.F4Pilot
