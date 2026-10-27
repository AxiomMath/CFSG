module

public import CFSG.LargeExtraspecial.S4SevenC
public import CFSG.LargeExtraspecial.S6OneB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_subgroupOf_resV_mul (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {h : S.M}
    (hth : t ∈ S.Lbar ((h : G) * g)) :
    ((S.Lbar ((h : G) * g)).subgroupOf (Rbar S g t)).map (resV haQ t) = LhmodN S g t h := by
  ext e
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact resV_mem_LhmodN haQ hth hl
  · rintro ⟨x, hx, hex⟩
    refine ⟨⟨x, Lbar_mul_le_Rbar hth hx⟩, hx, ?_⟩
    exact LinearEquiv.ext fun v => Subtype.ext ((coe_resV_apply haQ _ v).trans (hex v).symm)

theorem Rbar_le_sup_of_le_closure (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    {K₁ K₂ : Subgroup S.O}
    (hgen : RmodN S g t ≤ closure (((K₁.subgroupOf (Rbar S g t)).map (resV haQ t) :
      Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) ∪ (K₂.subgroupOf (Rbar S g t)).map (resV haQ t))) :
    Rbar S g t ≤ (K₁ ⊔ K₂) ⊔ Nbar S g t := by
  intro r hr
  set φ := resV haQ t with hφ
  have hφr : φ ⟨r, hr⟩ ∈ RmodN S g t := by rw [← range_resV haQ t]; exact ⟨_, rfl⟩
  have h1 := hgen hφr
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, ← Subgroup.map_sup] at h1
  obtain ⟨s, hs, hsr⟩ := h1
  have hsK : (s : S.O) ∈ K₁ ⊔ K₂ := by
    have := Subgroup.mem_map_of_mem (Rbar S g t).subtype hs
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at this
    exact (sup_le_sup (inf_le_left : K₁ ⊓ Rbar S g t ≤ K₁)
      (inf_le_left : K₂ ⊓ Rbar S g t ≤ K₂)) this
  have hN : ((s⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O) ∈ Nbar S g t := by
    rw [← resV_eq_one_iff haQ, map_mul, map_inv, hsr, inv_mul_cancel]
  have e : r = (s : S.O) * ((s⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O) := by simp
  rw [e]
  exact mul_mem (mem_sup_left hsK) (mem_sup_right hN)

section Gen

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
  (hk' : S.ρ k' ∈ Rbar S g t)
  (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
include H C ht ht1 hVQ hk hk' hkk'

theorem beta_bV_bV :
    beta H C ht ht1 hVQ (bV (mem_Lbar_mul_of_mem_Rbar H ht hk))
      (bV (mem_Lbar_mul_of_mem_Rbar H ht hk')) = 1 := by
  rcases zmod2_eq_zero_or_eq_one (beta H C ht ht1 hVQ (bV (mem_Lbar_mul_of_mem_Rbar H ht hk))
    (bV (mem_Lbar_mul_of_mem_Rbar H ht hk'))) with h0 | h1
  · exfalso
    rw [beta_bV_eq_zero_iff H C ht ht1 hVQ hk, coe_bV] at h0
    exact cl_not_mem_clSub_of_not_mem (S.z_mem_Qa (H.mul k).conj_mem (H.mul k).conj_ne)
      (conj_mem_QG' S k'.2 H.conj_mem) hkk' h0
  · exact h1

theorem Rbar_le_sup_of_omegaCase (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ) :
    Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  refine Rbar_le_sup_of_le_closure H.conj_mem ?_
  rw [map_subgroupOf_resV_mul H.conj_mem htk, map_subgroupOf_resV_mul H.conj_mem htk',
    LhmodN_eq_pointRadical H ht hk htk hX hE, LhmodN_eq_pointRadical H ht hk' htk' hX hE, hX]
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have hQ1 : ∀ {j : S.M} (hj : S.ρ j ∈ Rbar S g t) (htj : t ∈ S.Lbar ((j : G) * g)),
      Q (bV htj) = 0 := fun {j} hj htj =>
    (hsing _ (bV_ne_zero H htj)).mpr ⟨_, by rw [← range_resV H.conj_mem t]; exact ⟨⟨_, hj⟩, rfl⟩,
      resV_aV H.conj_mem ht hj htj⟩
  have hab : polar Q (bV htk) (bV htk') = 1 := by
    rw [← polarBilin_apply_apply, hpol]
    exact beta_bV_bV H C ht ht1 hVQ hk hk' hkk'
  have := S2.omegaFix_eq_closure_radFix hQ (F := ⊥) (by simp) (m := m) (by omega)
    (by rw [S2.perp_bot, finrank_top]; omega) (by simp) (by simp)
    (bV_ne_zero H htk) (hQ1 hk htk) (hQ1 hk' htk') hab
  rw [S2.omegaFix_bot, S2.radFix_bot, S2.radFix_bot] at this
  exact this.le

theorem Rbar_le_sup_of_spCase (hSp : SpCase H C ht ht1 hVQ) :
    Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  set β := beta H C ht ht1 hVQ with hβ
  have hβa := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  refine Rbar_le_sup_of_le_closure H.conj_mem ?_
  rw [map_subgroupOf_resV_mul H.conj_mem htk, map_subgroupOf_resV_mul H.conj_mem htk']
  have hLb : ∀ {j : S.M} (hj : S.ρ j ∈ Rbar S g t) (htj : t ∈ S.Lbar ((j : G) * g)),
      LhmodN S g t j = spPointRadical β (bV htj) := by
    intro j hj htj
    set e := resV H.conj_mem t ⟨S.ρ j, hj⟩ with he
    have heR : e ∈ RmodN S g t := by rw [← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
    have hea := resV_aV H.conj_mem ht hj htj
    have heI : e ∈ TauCeti.BilinForm.isometryGroup β := hSp.eq_sp ▸ heR
    rw [LhmodN_eq_map_conj H ht htj heR hea, hSp.LmodN_eq]
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      have := conj_mem_spPointRadical hβa heI hw
      rwa [hea] at this
    · intro w hw
      refine ⟨e⁻¹ * w * e, ?_, by simp [mul_assoc]⟩
      have hb' : e⁻¹ (bV htj) = aV ht := by
        rw [← hea]
        exact LinearEquiv.symm_apply_apply _ _
      have h1 := conj_mem_spPointRadical hβa (inv_mem heI) hw
      rwa [inv_inv, hb'] at h1
  rw [hLb hk htk, hLb hk' htk', hSp.eq_sp]
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have := S2.spFix_eq_closure_spRadFix hβa hnd (F := ⊥) (by simp) (m := m)
    (by rw [S2.spPerp_bot, finrank_top]; omega) (by simp) (by simp)
    (beta_bV_bV H C ht ht1 hVQ hk hk' hkk')
  rw [S2.spFix_bot, S2.spRadFix_bot, S2.spRadFix_bot] at this
  exact this.le

end Gen

theorem comm_mem_Lbar_inf_Nbar (H : Hyp4 S g) {t : S.O} {X : Subgroup S.O}
    (hX : X ∈ Dset S g t) {x y : S.O} (hx : x ∈ X) (hy : y ∈ Nbar S g t) :
    x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Nbar S g t := by
  have hnorm := Nbar_le_normalizer H.conj_mem H.conj_ne hX hy
  have hxR := le_Rbar hX hx
  obtain ⟨k', hk'⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hxR)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp hnorm _).mp (inv_mem hx)
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx h1
  · have hc := commute_of_mem_Rbar H.conj_mem hxR
    rw [← hk'] at hc ⊢
    exact mul_mem (conj_mem_Nbar H.conj_mem hc hy) (inv_mem hy)

theorem conj_mem_sup_of_mem (H : Hyp4 S g) {t : S.O} {X Y : Subgroup S.O}
    (hX : X ∈ Dset S g t) {x y : S.O} (hx : x ∈ X) (hy : y ∈ Y ⊓ Nbar S g t) :
    x * y * x⁻¹ ∈ (X ⊓ Nbar S g t) ⊔ (Y ⊓ Nbar S g t) := by
  have h1 := comm_mem_Lbar_inf_Nbar H hX hx hy.2
  rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
  exact mul_mem (mem_sup_left h1) (mem_sup_right hy)

theorem conj_mem_of_mem_Nbar (H : Hyp4 S g) {t : S.O} {X : Subgroup S.O}
    (hX : X ∈ Dset S g t) {x y : S.O} (hx : x ∈ Nbar S g t) (hy : y ∈ X ⊓ Nbar S g t) :
    x * y * x⁻¹ ∈ X ⊓ Nbar S g t := by
  have h1 := comm_mem_Lbar_inf_Nbar H hX hy.1 hx
  rw [show x * y * x⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ * y by group]
  exact mul_mem (inv_mem h1) hy

section Group

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
  (hk' : S.ρ k' ∈ Rbar S g t)
  (hgen : Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t)
  (hN0 : Nbar S g t = N0bar S g t)
include H ht hk hk' hgen hN0

theorem timmesfeld_6_5_N :
    Nbar S g t = (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊔ (S.Lbar ((k' : G) * g) ⊓ Nbar S g t) ∧
      Rbar S g t = S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hDa := Lbar_mul_mem_Dset htk
  have hDb := Lbar_mul_mem_Dset htk'
  set A := S.Lbar ((k : G) * g) ⊓ Nbar S g t with hA
  set B := S.Lbar ((k' : G) * g) ⊓ Nbar S g t with hB
  set P := A ⊔ B with hP
  have hPN : P ≤ Nbar S g t := sup_le inf_le_right inf_le_right
  have hnorm : (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t ≤
      normalizer (P : Set S.O) := by
    have key : ∀ x : S.O, (∀ y ∈ A, x * y * x⁻¹ ∈ P) → (∀ y ∈ B, x * y * x⁻¹ ∈ P) →
        x ∈ normalizer (P : Set S.O) := by
      intro x hxA hxB
      refine mem_normalizer_of_conj_le fun p hp => ?_
      have hle : P ≤ P.comap (MulAut.conj x).toMonoidHom :=
        sup_le (fun y hy => hxA y hy) (fun y hy => hxB y hy)
      exact hle hp
    refine sup_le (sup_le (fun x hx => key x (fun y hy => ?_) (fun y hy => ?_))
      (fun x hx => key x (fun y hy => ?_) (fun y hy => ?_)))
      (fun x hx => key x (fun y hy => ?_) (fun y hy => ?_))
    · refine mem_sup_left ?_
      rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
      exact mul_mem (comm_mem_Lbar_inf_Nbar H hDa hx hy.2) hy
    · exact conj_mem_sup_of_mem H hDa hx hy
    · rw [hP, sup_comm]
      exact conj_mem_sup_of_mem H hDb hx hy
    · refine mem_sup_right ?_
      rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
      exact mul_mem (comm_mem_Lbar_inf_Nbar H hDb hx hy.2) hy
    · exact mem_sup_left (conj_mem_of_mem_Nbar H hDa hx hy)
    · exact mem_sup_right (conj_mem_of_mem_Nbar H hDb hx hy)
  have hN0P : N0bar S g t ≤ P := by
    refine iSup₂_le fun j hj => ?_
    have hjk : S.ρ (j * k⁻¹) ∈ Rbar S g t := by
      rw [map_mul, map_inv]
      exact mul_mem hj (inv_mem hk)
    have hc := commute_of_mem_Rbar H.conj_mem hjk
    have hNmap : (Nbar S g t).map (MulAut.conj (S.ρ (j * k⁻¹))).toMonoidHom = Nbar S g t := by
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact conj_mem_Nbar H.conj_mem hc hx
      · refine ⟨(S.ρ (j * k⁻¹))⁻¹ * x * S.ρ (j * k⁻¹), ?_, by simp [mul_assoc]⟩
        have hc' : S.ρ (j * k⁻¹)⁻¹ * t = t * S.ρ (j * k⁻¹)⁻¹ := by
          rw [map_inv]
          exact commute_inv hc
        have := conj_mem_Nbar H.conj_mem hc' hx
        simpa [map_inv] using this
    have hcoe : (((j * k⁻¹ : S.M) : G) * ((k : G) * g)) = (j : G) * g := by
      simp [mul_assoc]
    have e : S.Lbar ((j : G) * g) ⊓ Nbar S g t =
        A.map (MulAut.conj (S.ρ (j * k⁻¹))).toMonoidHom := by
      rw [hA, Subgroup.map_inf_eq _ _ _ (MulAut.conj (S.ρ (j * k⁻¹))).injective, hNmap,
        ← Lbar_mul S (j * k⁻¹) ((k : G) * g), hcoe]
    rw [e]
    have hjP := hnorm (hgen hjk)
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hjP y).mp (mem_sup_left hy)
  have hNP : Nbar S g t = P := le_antisymm (hN0 ▸ hN0P) hPN
  refine ⟨hNP, le_antisymm ?_ (sup_le (Lbar_mul_le_Rbar htk) (Lbar_mul_le_Rbar htk'))⟩
  refine hgen.trans (sup_le le_rfl ?_)
  rw [hNP]
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem timmesfeld_6_5_inf (C : Cons311 S g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    S.Lbar ((k : G) * g) ⊓ S.Lbar ((k' : G) * g) = zpowers t := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hR := (timmesfeld_6_5_N H ht hk hk' hgen hN0).2
  refine le_antisymm ?_ ((zpowers_le).mpr ⟨htk, htk'⟩)
  have h47 := timmesfeld_4_7_c (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  rw [Rbar_mul] at h47
  rw [← h47]
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨?_, hx.1⟩
  rw [mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, hR] at hy
  have hle : S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g) ≤ centralizer ({x} : Set S.O) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · exact mem_centralizer_singleton_iff.mpr (Lbar_comm S (H.mul k).conj_mem hz hx.1)
    · exact mem_centralizer_singleton_iff.mpr (Lbar_comm S (H.mul k').conj_mem hz hx.2)
  exact mem_centralizer_singleton_iff.mp (hle hy)

end Group

end CFSG.LargeExtraspecial.S6
