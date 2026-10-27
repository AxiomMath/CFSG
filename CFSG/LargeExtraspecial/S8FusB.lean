module

public import CFSG.LargeExtraspecial.S8FusA
public import CFSG.LargeExtraspecial.S5Fus
public import CFSG.LargeExtraspecial.S6Six
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commSpace_conj (x t : S.O) :
    commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
  ext v
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w, sub_mem_commSpace _ _, ?_⟩
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (_ - _) = _
    rw [map_sub, apply_inv_apply_O]
    rfl
  · rintro ⟨_, hu, rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hu
    refine ⟨(x : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w))) - _ = _
    rw [inv_apply_apply_O, map_sub]
    rfl

theorem commSpace_le_Wt_of_fix {t τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t := by
  intro w hw
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
  refine mem_Wt.mpr fun v hv => ?_
  rw [polar_sub_right, ← hτV v hv,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2, hτV v hv, sub_self]

theorem apply_cl_eq_of_mem_normalizer (H : Hyp4 S g) {x : S.O} (hxN : x ∈ normalizer
    (S.Lbar g : Set S.O)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ fixSub S (S.Lbar g) := by
    refine (mem_fixSub S).mpr fun l hl => ?_
    have hl' : x⁻¹ * l * x ∈ S.Lbar g := (mem_normalizer_iff''.mp hxN l).mp hl
    have ha : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _
    have h1 := (mem_fixSub S).mp ha _ hl'
    change ((x⁻¹ * l * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _ at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
    calc (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl (g * S.z * g⁻¹))))) := (apply_inv_apply_O x _).symm
      _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by rw [h1]
  rw [H.fixSub_eq, Submodule.mem_span_singleton] at hfix
  obtain ⟨c, hc⟩ := hfix
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    rw [zero_smul] at hc
    have := congrArg (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hc
    rw [map_zero, inv_apply_apply_O] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this.symm
  · rw [one_smul] at hc
    exact hc.symm

section Alpha

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {Q : QuadraticForm (ZMod 2) (Vt S g t)}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hE : LmodN S g t = pointRadical Q (aV ht))
  (hQa : Q (aV ht) = 0)
  (hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
    2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width)
  (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
  {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
  (hPab : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t)
include H C ht ht1 hVQ hpol hE hQa hA hN hh hb hPab

theorem le_sup_of_fusion_alpha {τ : S.O} (hτL : τ ∈ S.Lbar g)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (haτ : S.cl (g * S.z * g⁻¹) ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hdim : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t)) (hτt : τ ≠ t)
    (hBτ : ∀ y ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t, y * τ = τ * y) :
    commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) := by
  set V1 := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hV1
  have hth := mem_Lbar_of_pair H ht hh
  have hbV := cl_mem_Vt hth
  have hbQ := conj_mem_QG' S h.2 H.conj_mem
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb hPab
  have hfixB := clSub_inf_fixSub_Abar (H.mul h) (C.mul h) hth ht1 (not_V_le_Qa_mul H hVQ hh)
    (card_Abar_mul H hh hA)
  rw [Nbar_mul, Vt_mul] at hfixB
  have hV1W : V1 ≤ Wt S g t := commSpace_le_Wt_of_fix hτV
  have hLV1 : ∀ l ∈ S.Lbar g, ∀ w ∈ V1, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ V1 := fun l hl w hw =>
    apply_mem_commSpace_of_commute (Lbar_comm S H.conj_mem hl hτL) hw
  have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ V1 :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr haτ
  have key : ∀ u ∈ V1, u ∈ Vt S g t → u ∉ S.clSub (S.QG ⊓ S.Qa g) → False := by
    intro u huV1 huV huP
    have hsub : ∀ d ∈ Vt S g t, d ∈ S.clSub (S.QG ⊓ S.Qa g) → d ∈ V1 := by
      intro d hdV hdP
      obtain ⟨l, hl, hld⟩ := exists_mem_Lbar_sub_sub_mem H C ht ht1 hVQ hpol hE hQa
        (u := ⟨u, huV⟩) (d := ⟨d, hdV⟩) huP hdP
      have h1 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ V1 := sub_mem (hLV1 l hl u huV1) huV1
      have e : d = ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) -
          ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u - d) := by abel
      rw [e]
      exact sub_mem h1 (hspan hld)
    have hle : Vt S g t ≤ V1 := by
      intro v hv
      by_cases hvP : v ∈ S.clSub (S.QG ⊓ S.Qa g)
      · exact hsub v hv hvP
      · have hb1 : beta H C ht ht1 hVQ (aV ht) ⟨u, huV⟩ = 1 := zmod2_eq_one_of_ne_zero
          fun h0 => huP ((beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp h0)
        have hb2 : beta H C ht ht1 hVQ (aV ht) ⟨v, hv⟩ = 1 := zmod2_eq_one_of_ne_zero
          fun h0 => hvP ((beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp h0)
        have hb3 : beta H C ht ht1 hVQ (aV ht) (⟨v, hv⟩ - ⟨u, huV⟩) = 0 := by
          rw [map_sub, hb1, hb2, sub_self]
        have hvu := (beta_aV_eq_zero_iff H C ht ht1 hVQ _).mp hb3
        have e : v = (v - u) + u := by abel
        rw [e]
        exact add_mem (hsub _ (sub_mem hv huV) hvu) huV1
    have heq : V1 = Vt S g t := (Submodule.eq_of_le_of_finrank_le hle hdim.le).symm
    exact hτt (eq_t_of_commSpace_eq H C ht ht1 hVQ hτL heq)
  intro w hw
  have hwW := hV1W hw
  rw [← hdec] at hwW
  obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.mp hwW
  by_cases hβV : β ∈ Vt S g t
  · rw [add_comm]
    exact Submodule.add_mem_sup hβV hα
  · exfalso
    obtain ⟨y, hy, hyβ⟩ : ∃ y ∈ S.Lbar ((h : G) * g) ⊓ Nbar S g t,
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) β ≠ β := by
      by_contra hcon
      push Not at hcon
      have hmem : β ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓
          fixSub S (S.Lbar ((h : G) * g) ⊓ Nbar S g t) := ⟨hβ.1, (mem_fixSub S).mpr hcon⟩
      rw [hfixB] at hmem
      exact hβV hmem.2
    have hyb : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) β - β =
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (Lbar_apply_sub_mem_span' (H.mul h).conj_mem hβ.1 hy.1)
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc
        exact absurd (sub_eq_zero.mp hc.symm) hyβ
      · rw [one_smul] at hc
        exact hc.symm
    have hyα1 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α ∈ Vt S g t := hN y hy.2 α hα.2
    have hyα2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α ∈ S.clSub (S.QG ⊓ S.Qa g) :=
      sub_mem (Nbar_apply_mem_clSub H.conj_mem H.conj_ne (cl_a_mem_Vt ht) hy.2 hα.1) hα.1
    have huV1 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) - (α + β) ∈ V1 :=
      sub_mem (apply_mem_commSpace_of_commute (hBτ y hy) hw) hw
    have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) - (α + β) =
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α) + S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
      rw [← hyb, map_add]; abel
    rw [e] at huV1
    refine key _ huV1 (add_mem hyα1 hbV) fun hP => ?_
    have := sub_mem hP hyα2
    rw [add_sub_cancel_left] at this
    exact cl_b_not_mem H hb this

theorem fusion_alpha
    (hNc : ∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t)
    {τ : S.O} (hτA : τ ∈ S.Lbar g ⊓ Nbar S g t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hxτ : τ = x * t * x⁻¹) (hτt : τ ≠ t) :
    ∃ n ∈ Nbar S g t, n * τ * n⁻¹ = τ * t := by
  by_contra hcon
  push Not at hcon
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  have hτtc : τ * t = t * τ := Lbar_comm S H.conj_mem hτA.1 ht
  have hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n := by
    intro n hn
    rcases eq_one_or_eq_of_mem_zpowers htt (hNc n hn τ hτA.2) with h1 | h1
    · calc n * τ = n * τ * n⁻¹ * τ⁻¹ * (τ * n) := by group
        _ = τ * n := by rw [h1, one_mul]
    · exfalso
      apply hcon n hn
      calc n * τ * n⁻¹ = n * τ * n⁻¹ * τ⁻¹ * τ := by group
        _ = t * τ := by rw [h1]
        _ = τ * t := hτtc.symm
  obtain ⟨y, hyM, hyN, hyτ⟩ := S5.exists_mem_normalizer_conj H C hxM
    (fun l hl => Lbar_comm S H.conj_mem ht hl)
    (fun l hl => by rw [← hxτ]; exact Lbar_comm S H.conj_mem hτA.1 hl)
  rw [← hxτ] at hyτ
  have hya := apply_cl_eq_of_mem_normalizer H hyN
  have hyia : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    conv_lhs => rw [← hya]
    exact inv_apply_apply_O y _
  have hyP : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      S.clSub (S.QG ⊓ S.Qa g) := fun v hv =>
    apply_mem_clSub_of_fix H.conj_mem H.conj_ne hyM hya hv
  have hyiP : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      S.clSub (S.QG ⊓ S.Qa g) := fun v hv =>
    apply_mem_clSub_of_fix H.conj_mem H.conj_ne (inv_mem hyM) hyia hv
  set V1 := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hV1
  have hV1eq : V1 = (Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hV1, hyτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdim : finrank (ZMod 2) V1 = finrank (ZMod 2) (Vt S g t) := by
    rw [hV1eq]
    exact LinearEquiv.finrank_map_eq _ _
  have hmemV1 : ∀ v ∈ Vt S g t, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V1 := fun v hv => by
    rw [hV1eq]; exact ⟨v, hv, rfl⟩
  have haV1 : S.cl (g * S.z * g⁻¹) ∈ V1 := by
    rw [← hya]; exact hmemV1 _ (cl_a_mem_Vt ht)
  have hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Nbar.mp hτA.2).2
  have hle := le_sup_of_fusion_alpha H C ht ht1 hVQ hpol hE hQa hA hN hh hb hPab hτA.1 hτV
    haV1 hdim hτt fun y' hy' => hcN y' hy'.2
  obtain ⟨w₀, hw₀, hw₀P⟩ : ∃ w ∈ V1, w ∉ S.clSub (S.QG ⊓ S.Qa g) := by
    by_contra hcon'
    push Not at hcon'
    apply hVQ
    rw [V_le_Qa_iff H.conj_mem H.conj_ne]
    intro v hv
    have := hyiP _ (hcon' _ (hmemV1 v hv))
    rwa [inv_apply_apply_O] at this
  obtain ⟨v₀, hv₀, α₀, hα₀, rfl⟩ := Submodule.mem_sup.mp (hle hw₀)
  have hv₀P : v₀ ∉ S.clSub (S.QG ⊓ S.Qa g) := fun hP => hw₀P (add_mem hP hα₀.1)
  have hPV : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t ≤ V1 := by
    rintro d ⟨hdP, hdV⟩
    obtain ⟨l, hl, hld⟩ := exists_mem_Lbar_sub_sub_mem H C ht ht1 hVQ hpol hE hQa
      (u := ⟨v₀, hv₀⟩) (d := ⟨d, hdV⟩) hv₀P hdP
    have h1 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (v₀ + α₀) - (v₀ + α₀) ∈ V1 :=
      sub_mem (apply_mem_commSpace_of_commute (Lbar_comm S H.conj_mem hl hτA.1) hw₀) hw₀
    have h2 := Lbar_apply_sub_mem_span' H.conj_mem hα₀.1 hl
    have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ V1 :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr haV1
    have e : d = ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) (v₀ + α₀) - (v₀ + α₀)) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) v₀ - v₀ - d) -
        ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) α₀ - α₀) := by rw [map_add]; abel
    rw [e]
    exact sub_mem (sub_mem h1 (hspan hld)) (hspan h2)
  have hPV1 : S.clSub (S.QG ⊓ S.Qa g) ⊓ V1 = S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    have hmap : S.clSub (S.QG ⊓ S.Qa g) ⊓ V1 =
        (S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t).map (y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
      apply le_antisymm
      · rintro w ⟨hwP, hwV1⟩
        rw [hV1eq] at hwV1
        obtain ⟨v, hv, rfl⟩ := hwV1
        refine ⟨v, ⟨?_, hv⟩, rfl⟩
        have := hyiP _ hwP
        rwa [show ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((y : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap v) = v from inv_apply_apply_O y v] at this
      · rintro _ ⟨v, ⟨hvP, hv⟩, rfl⟩
        exact ⟨hyP v hvP, hmemV1 v hv⟩
    have hd : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ V1) =
        finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t) := by
      rw [hmap]; exact LinearEquiv.finrank_map_eq _ _
    exact (Submodule.eq_of_le_of_finrank_le (le_inf inf_le_left hPV) hd.le).symm
  have hAV1 : ∀ a' ∈ S.Lbar g ⊓ Nbar S g t, ∀ w ∈ V1, (a' : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro a' ha' w hw
    rw [hV1eq] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    set a'' := y⁻¹ * a' * y with ha''
    have ha''L : a'' ∈ S.Lbar g := (mem_normalizer_iff''.mp hyN a').mp ha'.1
    have ha''A : a'' ∈ S.Lbar g ⊓ Nbar S g t := by
      refine mem_Abar_of_fix H C ht ht1 hVQ hA ha''L fun d hd => ?_
      have hyd : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
        rw [← hPV1]; exact ⟨hyP d hd.1, hmemV1 d hd.2⟩
      change ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) d)) = d
      rw [(mem_Nbar.mp ha'.2).2 _ hyd.2, inv_apply_apply_O]
    have h1 : (a'' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Nbar.mp ha''A.2).2 v hv
    change ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((a' : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v at h1
    have := congrArg (y : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at this
  have hfixA := clSub_inf_fixSub_Abar H C ht ht1 hVQ hA
  have hV1V : V1 ≤ Vt S g t := by
    intro w hw
    obtain ⟨v, hv, α, hα, rfl⟩ := Submodule.mem_sup.mp (hle hw)
    have hαfix : α ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) := by
      refine ⟨hα.1, (mem_fixSub S).mpr fun a' ha' => ?_⟩
      have h1 := hAV1 a' ha' _ hw
      have h2 := (mem_Nbar.mp ha'.2).2 v hv
      rw [map_add, h2] at h1
      exact add_left_cancel h1
    rw [hfixA] at hαfix
    exact add_mem hv hαfix.2
  have heq : V1 = Vt S g t := Submodule.eq_of_le_of_finrank_le hV1V hdim.ge
  exact hτt (eq_t_of_commSpace_eq H C ht ht1 hVQ hτA.1 heq)

end Alpha

end CFSG.LargeExtraspecial.S8
