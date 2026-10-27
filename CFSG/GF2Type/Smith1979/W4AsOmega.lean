module

public import CFSG.GF2Type.Smith1979.W4AsKern
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S8FusA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_inf_Nbar_eq_zpowers (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    S.Lbar g ⊓ Nbar S g t = zpowers t := by
  have hLm : Nat.card (LmodN S g t) = 4 := by
    obtain ⟨Qf, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
    have hQa : Qf (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
    rw [hE, card_pointRadical hQ (aV_ne_zero H ht) hQa, h4]
    norm_num
  have h1 := S6.card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, hLm, hw] at h1
  have hcard : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) = 2 := by
    have h8 : (2 : ℕ) ^ (4 - 1) = 8 := by norm_num
    rw [h8] at h1
    omega
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t :=
    le_inf (zpowers_le.mpr ht) (zpowers_le.mpr (S6.self_mem_Nbar H ht))
  exact (eq_of_le_of_card_ge hle (by rw [hcard, S7.card_zpowers_eq_two H ht ht1])).symm

theorem Nbar_eq_zpowers_omega4 (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) : Nbar S g t = zpowers t :=
  S14.Nbar_eq_zpowers_of_N0bar H ht (S6.Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ)
    (Lbar_inf_Nbar_eq_zpowers hw H C ht ht1 hVQ hΩ h4)

theorem resCV_mem_orthogonalGroup_omega (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
    (x : S8.CMt S t) :
    S8.resCV S g H.conj_mem t x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  have hD := dtEqConj_of_omegaCase H hNo C hΩ
  have key : ∀ y ∈ S8.CMt S t, ∀ v : S.Qt, v ∈ orbit S g t →
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := fun y hy v hv =>
    S7.apply_mem_orbit_of_comm H ht hD (S8.mem_CMt.mp hy).1 (S8.mem_CMt.mp hy).2 hv
  have z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  intro v
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hcv0 : S8.resCV S g H.conj_mem t x v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv0
  have hiff : Q (S8.resCV S g H.conj_mem t x v) = 0 ↔ Q v = 0 := by
    rw [hsing _ hcv0, hsing _ hv0, mem_orbitOf_RmodN_iff H.conj_mem ht,
      mem_orbitOf_RmodN_iff H.conj_mem ht, S8.coe_resCV_apply]
    constructor
    · intro h
      have := key _ (inv_mem x.2) _ h
      rwa [inv_apply_apply_O] at this
    · exact key _ x.2 _
  rcases z2 (Q (S8.resCV S g H.conj_mem t x v)) with h1 | h1 <;> rcases z2 (Q v) with h2 | h2
  · rw [h1, h2]
  · exact absurd (hiff.mp h1) (by rw [h2]; decide)
  · exact absurd (hiff.mpr h2) (by rw [h1]; decide)
  · rw [h1, h2]

theorem comm_mem_Nbar_of_fix (H : Hyp4 S g) {t c : S.O} (hcM : c ∈ S.Mbar)
    (hct : c * t = t * c) (hcV : ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {r : S.O}
    (hr : r ∈ Rbar S g t) : r * c * r⁻¹ * c⁻¹ ∈ Nbar S g t := by
  obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hcM
  refine mem_Nbar.mpr ⟨?_, fun v hv => ?_⟩
  · rw [show r * S.ρ κ * r⁻¹ * (S.ρ κ)⁻¹ = r * (S.ρ κ * r⁻¹ * (S.ρ κ)⁻¹) by group]
    exact mul_mem hr (conj_mem_Rbar hct (inv_mem hr))
  · have h1 : (((S.ρ κ)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      conv_lhs => rw [← hcV v hv]
      exact inv_apply_apply_O _ v
    have h2 := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hr) hv
    simp only [coe_mul_apply, h1, hcV _ h2, apply_inv_apply_O]

theorem eq_one_of_fixes_D_omega (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {k : S.O} (hkM : k ∈ S.Mbar)
    (hkL : ∀ l ∈ S.Lbar g, k * l = l * k)
    (hkD : ∀ d ∈ S.clSub (S.QG ⊓ S.Qa g), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d) : k = 1 := by
  have haQ := H.conj_mem
  have hN := Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have hD := dtEqConj_of_omegaCase H hNo C hΩ
  have hkt : k * t = t * k := hkL t ht
  have hkCM : k ∈ S8.CMt S t := S8.mem_CMt.mpr ⟨hkM, hkt⟩
  obtain ⟨Qf, hQ, hpol, -, -, hsing⟩ := hΩ.exists_form
  have hQa : Qf (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
  have hκ : S8.resCV S g haQ t ⟨k, hkCM⟩ = 1 := by
    refine eq_one_of_fix_orthogonal_of_map_eq_zero hQ hQa
      (resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ hsing ⟨k, hkCM⟩) fun y hy => ?_
    have hy' : beta H C ht ht1 hVQ (aV ht) y = 0 := by
      rw [← hpol, polarBilin_apply_apply]
      exact hy
    exact Subtype.ext (hkD _ ((beta_aV_eq_zero_iff H C ht ht1 hVQ y).mp hy'))
  have hkV : ∀ v ∈ Vt S g t, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    congrArg (fun e : Vt S g t ≃ₗ[ZMod 2] Vt S g t => ((e ⟨v, hv⟩ : Vt S g t) : S.Qt)) hκ
  have hmem : ∀ r ∈ Rbar S g t, r * k * r⁻¹ * k⁻¹ ∈ zpowers t := fun r hr =>
    hN ▸ comm_mem_Nbar_of_fix H hkM hkt hkV hr
  have hconj : ∀ r ∈ Rbar S g t, ∀ l ∈ S.Lbar g, k * (r * l * r⁻¹) = r * l * r⁻¹ * k := by
    intro r hr l hl
    have hc := hmem r⁻¹ (inv_mem hr)
    rw [inv_inv] at hc
    set c := r⁻¹ * k * r * k⁻¹ with hcdef
    have hcL : c ∈ S.Lbar g := zpowers_le.mpr ht hc
    have e1 : k = r * (c * k) * r⁻¹ := by rw [hcdef]; group
    calc k * (r * l * r⁻¹) = r * (c * k) * r⁻¹ * (r * l * r⁻¹) := by rw [← e1]
      _ = r * (c * (k * l)) * r⁻¹ := by group
      _ = r * (c * (l * k)) * r⁻¹ := by rw [hkL l hl]
      _ = r * ((c * l) * k) * r⁻¹ := by group
      _ = r * ((l * c) * k) * r⁻¹ := by rw [S.Lbar_comm haQ hcL hl]
      _ = r * l * r⁻¹ * (r * (c * k) * r⁻¹) := by group
      _ = r * l * r⁻¹ * k := by rw [← e1]
  have hcent : Rbar S g t ≤ centralizer ({k} : Set S.O) := by
    refine (Rbar_le_closure_conj hD).trans ((closure_le _).mpr ?_)
    rintro _ ⟨r, hr, l, hl, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hconj r hr l hl).symm
  by_contra hk1
  set U := commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hk1
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have h0 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ U := mem_commSpace.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h0
    exact h0
  have hVU : Vt S g t ≤ U := Vt_le_of_invariant H hUne fun x hx u hu =>
    S6.apply_mem_commSpace_of_commute (mem_centralizer_singleton_iff.mp (hcent hx)) hu
  have hUD : U ≤ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [← S6.orthogonal_clSub_eq haQ H.conj_ne C.card_QG_inf_Qa]
    intro u hu
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    refine W4C1.Par.mem_perp.mpr fun d hd => ?_
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup k.2 d v
    rw [hkD d hd] at h1
    rw [polar_sub_right, ← h1, sub_self]
  have hle : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := le_inf (hVU.trans hUD) le_rfl
  have h1 := S6.finrank_clSub_inf_Vt H C ht ht1 hVQ
  have h2 := Submodule.finrank_mono hle
  omega

theorem gen4_of_omega (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (C : Cons311 S g) (hNo : NoA2 S g) (_hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) : CFSG.GH74.SectionalTwoRankLE S.Mbar 4 :=
  sectionalTwoRankLE_Mbar_of_K_trivial hw H C fun _ hkM hkD =>
    eq_one_of_fixes_D_omega hCE hw H hNo C ht ht1 hVQ hΩ h4 hkM
      (fun _ hl => commute_of_mem_K H C hkM hkD hl) hkD

end CFSG.GF2Type.Smith1979.W4As
