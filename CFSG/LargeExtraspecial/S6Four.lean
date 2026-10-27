module

public import CFSG.LargeExtraspecial.S6ThreeE
public import CFSG.LargeExtraspecial.S2ThreeDual

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

section Codim

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem sup_span_eq_of_finrank_eq {X Y : Submodule (ZMod 2) U} (hXY : X ≤ Y)
    (hdim : finrank (ZMod 2) Y = finrank (ZMod 2) X + 1) {y : U} (hy : y ∈ Y) (hyX : y ∉ X) :
    X ⊔ (ZMod 2) ∙ y = Y := by
  have hlt : X < X ⊔ (ZMod 2) ∙ y := lt_of_le_of_ne le_sup_left fun h =>
    hyX (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  refine Submodule.eq_of_le_of_finrank_le
    (sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hy)) ?_
  omega

theorem apply_sub_mem_of_finrank_eq (e : U ≃ₗ[ZMod 2] U) {X Y : Submodule (ZMod 2) U}
    (hXY : X ≤ Y) (hdim : finrank (ZMod 2) Y = finrank (ZMod 2) X + 1)
    (hX : ∀ v ∈ X, e v ∈ X) (hY : ∀ v ∈ Y, e v ∈ Y) {y : U} (hy : y ∈ Y) : e y - y ∈ X := by
  by_cases hyX : y ∈ X
  · exact sub_mem (hX y hyX) hyX
  have hey : e y ∈ X ⊔ (ZMod 2) ∙ y := (sup_span_eq_of_finrank_eq hXY hdim hy hyX).symm ▸ hY y hy
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hey
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    rw [zero_smul, add_zero] at hvw
    have hmap : X.map e.toLinearMap = X := Submodule.eq_of_le_of_finrank_eq
      (by rintro _ ⟨v, hv, rfl⟩; exact hX v hv) (LinearEquiv.finrank_map_eq e X)
    have hm : e y ∈ X.map e.toLinearMap := hmap.symm ▸ (hvw ▸ hv)
    obtain ⟨y', hy', hy'e⟩ := hm
    exact hyX (e.injective hy'e ▸ hy')
  · rw [one_smul] at hvw
    rw [← hvw, add_sub_cancel_right]
    exact hv

end Codim

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def resW (H : Hyp4 S g) (t : S.O) :
    Rbar S g t →* (Wt S g t ≃ₗ[ZMod 2] Wt S g t) :=
  restrictHom (S.O.subtype.comp (Rbar S g t).subtype) (Wt S g t)
    (fun x _ hu => apply_mem_Wt H x.2 hu)

theorem coe_resW_apply (H : Hyp4 S g) {t : S.O} (x : Rbar S g t) (w : Wt S g t) :
    ((resW S g H t x w : Wt S g t) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w :=
  rfl

theorem resW_eq_one_iff (H : Hyp4 S g) {t : S.O} (x : Rbar S g t) :
    resW S g H t x = 1 ↔ ∀ w ∈ Wt S g t, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w :=
  restrictHom_eq_one_iff (S.O.subtype.comp (Rbar S g t).subtype) (Wt S g t)
    (fun x _ hu => apply_mem_Wt H x.2 hu) x

section Four

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

theorem Nbar_eq_zpowers_of_width (hn : S.width = finrank (ZMod 2) (Vt S g t) + 1) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    Nbar S g t = zpowers t := by
  have hc := card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp
  rw [show S.width - finrank (ZMod 2) (Vt S g t) = 1 by omega, pow_one] at hc
  have hct : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem ht) ht1
  have hLa : zpowers t = S.Lbar g ⊓ Nbar S g t :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ⟨ht, self_mem_Nbar H ht⟩) (by rw [hc, hct])
  have hLb : zpowers t = S.Lbar ((h : G) * g) ⊓ Nbar S g t :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ⟨mem_Lbar_of_pair H ht hh, self_mem_Nbar H ht⟩)
      (by rw [card_Lbar_mul_inf_Nbar H hh, hc, hct])
  rw [Nbar_eq_sup_sp hCE H hNo C ht ht1 hVQ hSp hh hb, ← hLa, ← hLb, sup_idem]

theorem timmesfeld_6_4_width : finrank (ZMod 2) (Vt S g t) + 1 < S.width := by
  by_contra hcon
  push Not at hcon
  have hwd := finrank_Vt_le_width H ht1
  obtain ⟨r, hr⟩ := odd_width_sp hCE H hNo C ht ht1 hVQ hSp
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have hn : S.width = finrank (ZMod 2) (Vt S g t) + 1 := by omega
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have dV1 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  have dW1 := finrank_Wone (S := S) (g := g) (t := t) g ((h : G) * g)
  have dW := finrank_Wt (S := S) (g := g) (t := t)
  have dQ := S.finrank_Qt_eq_two_mul_width
  have hV1W1 : Vone S g t g ((h : G) * g) = Wone S g t g ((h : G) * g) :=
    Submodule.eq_of_le_of_finrank_le (Vone_le_Wone H C ht ht1 hVQ hh hb) (by omega)
  have hNt := Nbar_eq_zpowers_of_width hCE H hNo C ht ht1 hVQ hSp hn hh hb
  have htW : ∀ w ∈ Wt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw =>
    mem_fixSpace.mp (((commSpace_t_eq H C ht ht1 hVQ).2).symm ▸ hw)
  let K : Subgroup S.O :=
    { carrier := {x | ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w}
      mul_mem' := fun {x y} hx hy w hw => by
        rw [coe_mul_apply, hy w hw, hx w hw]
      one_mem' := fun w _ => rfl
      inv_mem' := fun {x} hx w hw => by
        conv_lhs => rw [← hx w hw]
        exact inv_apply_apply_O x w }
  have hNW : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro x hx
    rw [hNt] at hx
    exact (zpowers_le.mpr (show t ∈ K from htW)) hx
  have hR : ∀ x ∈ Rbar S g t, ∀ w ∈ Wt S g t,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro x hx w hw
    have hV1x : ∀ v ∈ Vone S g t g ((h : G) * g),
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g) :=
      fun v hv => apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hx hv
    have hVx : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t :=
      fun v hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv
    have h1 := apply_sub_mem_of_finrank_eq (x : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (Vone_le_Wt H C ht ht1 hVQ hh hb) (by omega) hV1x (fun v hv => apply_mem_Wt H hx hv) hw
    have h2 : ∀ v ∈ Vone S g t g ((h : G) * g), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t :=
      fun v hv => apply_sub_mem_of_finrank_eq (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (Vt_le_Vone _ _) dV1
        hVx hV1x hv
    by_contra hu
    set u := (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w with hu_def
    have hq := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 w
    have hxw : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + u := by rw [hu_def]; abel
    rw [hxw, QuadraticMap.map_add S.q w u, q_eq_zero_of_mem_Vone H C ht ht1 hVQ hh hb h1,
      add_zero] at hq
    have hpol : polar S.q w u = 0 := by
      have := congrArg (· - S.q w) hq
      simpa using this
    have hspan := sup_span_eq_of_finrank_eq (Vt_le_Vone _ _) dV1 h1 hu
    have hwW1 : w ∈ Wone S g t g ((h : G) * g) := by
      rw [mem_Wone]
      intro v hv
      rw [← hspan] at hv
      obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb'
      rw [polar_add_left, polar_smul_left, mem_Wt.mp hw a ha, polar_comm, hpol, smul_eq_mul,
        mul_zero, add_zero]
    exact hu (h2 w (hV1W1 ▸ hwW1))
  have hker : (resV H.conj_mem t).ker ≤ (resW S g H t).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, resV_eq_one_iff] at hx
    rw [MonoidHom.mem_ker, resW_eq_one_iff]
    exact hNW _ hx
  set β := beta H C ht ht1 hVQ with hβ
  have hrange : (resV H.conj_mem t).range = TauCeti.BilinForm.isometryGroup β :=
    (range_resV H.conj_mem t).trans hSp.eq_sp
  set ρ : TauCeti.BilinForm.isometryGroup β →* (Wt S g t ≃ₗ[ZMod 2] Wt S g t) :=
    (descend (resV H.conj_mem t) (resW S g H t) hker).comp
      (MulEquiv.subgroupCongr hrange.symm).toMonoidHom with hρdef
  have hρ : ∀ (e : TauCeti.BilinForm.isometryGroup β) (x : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x → ρ e = resW S g H t x :=
    fun e x hex => descend_apply' (resV H.conj_mem t) (resW S g H t) hker
      (e := (MulEquiv.subgroupCongr hrange.symm).toMonoidHom e) hex
  have hρe : ∀ e : TauCeti.BilinForm.isometryGroup β,
      ∃ x : Rbar S g t, (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x := by
    intro e
    have : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV H.conj_mem t).range := by
      rw [hrange]
      exact e.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx.symm⟩
  set ι : Vt S g t →ₗ[ZMod 2] Wt S g t := Submodule.inclusion (Vt_le_Wt H ht1) with hι
  have hιinj : Function.Injective ι := Submodule.inclusion_injective _
  have hιρ : ∀ (e : TauCeti.BilinForm.isometryGroup β) (v : Vt S g t),
      ρ e (ι v) = ι ((e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) v) := by
    intro e v
    obtain ⟨x, hx⟩ := hρe e
    rw [hρ e x hx, hx]
    rfl
  have hcomm : ∀ (e : TauCeti.BilinForm.isometryGroup β) (w : Wt S g t),
      ρ e w - w ∈ LinearMap.range ι := by
    intro e w
    obtain ⟨x, hx⟩ := hρe e
    rw [hρ e x hx]
    refine ⟨⟨_, hR x x.2 w w.2⟩, Subtype.ext ?_⟩
    rfl
  have hind : S2.IsIndecomposable ρ := by
    intro A B hA hB hAB
    by_contra hne
    push Not at hne
    have hfix : ∀ D : Submodule (ZMod 2) (Wt S g t), (∀ e, ∀ v ∈ D, ρ e v ∈ D) → D ≠ ⊥ →
        S.cl (g * S.z * g⁻¹) ∈ D.map (Wt S g t).subtype := by
      intro D hD hD0
      have hinv : ∀ l ∈ S.Lbar g, ∀ u ∈ D.map (Wt S g t).subtype,
          (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ D.map (Wt S g t).subtype := by
        rintro l hl _ ⟨d, hd, rfl⟩
        have hxR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
        have hxe : resV H.conj_mem t ⟨l, hxR⟩ ∈ TauCeti.BilinForm.isometryGroup β := by
          rw [← hrange]
          exact ⟨_, rfl⟩
        have h1 := hD ⟨_, hxe⟩ d hd
        rw [hρ ⟨_, hxe⟩ ⟨l, hxR⟩ rfl] at h1
        exact ⟨_, h1, rfl⟩
      have hne' : D.map (Wt S g t).subtype ≠ ⊥ := by
        obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD0
        intro h0
        have : ((d : Wt S g t) : S.Qt) ∈ D.map (Wt S g t).subtype := ⟨d, hd, rfl⟩
        rw [h0, Submodule.mem_bot] at this
        exact hd0 (Subtype.ext this)
      obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_of_isPGroup S (isPGroup_Lbar S H.conj_mem)
        hinv hne'
      have hfx : u ∈ fixSub S (S.Lbar g) := hufix
      have hua : u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := H.fixSub_eq ▸ hfx
      rcases mem_span_cl_iff.mp hua with h0 | rfl
      · exact absurd h0 hu0
      · exact hu
    have ha := hfix A hA hne.1
    have hb' := hfix B hB hne.2
    have hinf : A.map (Wt S g t).subtype ⊓ B.map (Wt S g t).subtype = ⊥ := by
      rw [← Submodule.map_inf _ (Wt S g t).injective_subtype, hAB.inf_eq_bot, Submodule.map_bot]
    have : S.cl (g * S.z * g⁻¹) ∈ (⊥ : Submodule (ZMod 2) S.Qt) := hinf ▸ ⟨ha, hb'⟩
    rw [Submodule.mem_bot] at this
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne this
  have hle := S2.sp_timmesfeld_2_3_2 ρ (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) h4 hind hιinj hιρ hcomm
  omega

theorem timmesfeld_6_4 : zpowers t < S.Lbar g ⊓ Nbar S g t := by
  refine lt_of_le_of_ne (zpowers_le.mpr ⟨ht, self_mem_Nbar H ht⟩) fun he => ?_
  have h1 := timmesfeld_6_4_width hCE H hNo C ht ht1 hVQ hSp
  have hc := card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp
  have hct : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem ht) ht1
  rw [← he, hct] at hc
  have h2 : 2 ^ 1 = 2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) := by
    rw [pow_one]
    exact hc
  have := Nat.pow_right_injective le_rfl h2
  omega

end Four

end CFSG.LargeExtraspecial.S6
