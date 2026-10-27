module

public import CFSG.LargeExtraspecial.S6NQB
public import CFSG.LargeExtraspecial.S2SpOne
public import CFSG.LargeExtraspecial.S2OrthOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

section Generic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem radDecomp_bot_of_isCompl {q : QuadraticForm (ZMod 2) V}
    {hq : q.polarBilin.Nondegenerate} {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}
    (h : IsCompl (S2.fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (S2.fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    S2.RadDecomp ρ ⊥ ⊤ p p₁ := by
  rw [S2.RadDecomp, S2.radFix_bot, S2.radFix_bot, top_inf_eq, top_inf_eq]
  exact ⟨h.sup_eq_top, h.inf_eq_bot⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadDecomp_bot_of_isCompl {f : LinearMap.BilinForm (ZMod 2) V}
    {ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M)} {p p₁ : V}
    (h : IsCompl (S2.fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)))
      (S2.fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    S2.SpRadDecomp ρ ⊥ ⊤ p p₁ := by
  rw [S2.SpRadDecomp, S2.spRadFix_bot, S2.spRadFix_bot, top_inf_eq, top_inf_eq]
  exact ⟨h.sup_eq_top, h.inf_eq_bot⟩

end Generic

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem pairGen_of_omegaCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) : PairGen S g t :=
  fun _ _ hk hk' hkk' => Rbar_le_sup_of_omegaCase H C ht ht1 hVQ hk hk' hkk' hNo hΩ

theorem pairGen_of_spCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) : PairGen S g t :=
  fun _ _ hk hk' hkk' => Rbar_le_sup_of_spCase H C ht ht1 hVQ hk hk' hkk' hSp

theorem pair_one {t : S.O} {h : S.M}
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    S.ρ 1 ∈ Rbar S g t ∧ ((h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa (((1 : S.M) : G) * g)) :=
  ⟨by rw [map_one]; exact one_mem _, by simpa using hb⟩

section Five

variable (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : PairGen S g t)
  (hN0 : Nbar S g t = N0bar S g t) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include H C ht ht1 hVQ hgen hN0 hh hb

theorem timmesfeld_6_5_bar :
    Nbar S g t = (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((h : G) * g) ⊓ Nbar S g t) ∧
      S.Lbar g ⊓ S.Lbar ((h : G) * g) = zpowers t := by
  have h1 := pair_one (t := t) hb
  have hgen' := hgen 1 h h1.1 hh h1.2
  have hA := timmesfeld_6_5_N H ht h1.1 hh hgen' hN0
  have hB := timmesfeld_6_5_inf H ht h1.1 hh hgen' hN0 C ht1 hVQ
  simp only [OneMemClass.coe_one, one_mul] at hA hB
  exact ⟨hA.1, hB⟩

omit C ht1 hVQ in
theorem timmesfeld_6_5_one :
    N S g t = (S.La g ⊓ N S g t) ⊔ (S.La ((h : G) * g) ⊓ N S g t) := by
  have hth := mem_Lbar_of_pair H ht hh
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right inf_le_right)
  obtain ⟨hxM, hxN⟩ := (mem_N_iff ht).mp hx
  have h1 := pair_one (t := t) hb
  obtain ⟨y, hy, w, hw, hyw⟩ := exists_mul_of_pair H ht h1.1 hh
    (hgen 1 h h1.1 hh h1.2) hN0 hxN
  simp only [OneMemClass.coe_one, one_mul] at hy
  obtain ⟨y₀, hy₀L, rfl⟩ := (mem_Lbar S).mp hy.1
  obtain ⟨w₀, hw₀L, rfl⟩ := (mem_Lbar S).mp hw.1
  have hQN : S.QG ≤ N S g t := fun q hq => (mem_N_iff ht).mpr ⟨S.QG_le_M hq, by
    rw [(S.ρ_eq_one_iff ⟨q, S.QG_le_M hq⟩).mpr hq]; exact one_mem _⟩
  have hy₀N : (y₀ : G) ∈ N S g t := (mem_N_iff ht).mpr ⟨y₀.2, hy.2⟩
  have hw₀N : (w₀ : G) ∈ N S g t := (mem_N_iff ht).mpr ⟨w₀.2, hw.2⟩
  have hq : ((y₀ : G) * w₀)⁻¹ * x ∈ S.QG := by
    have e : S.ρ ((y₀ * w₀)⁻¹ * ⟨x, hxM⟩) = 1 := by
      rw [map_mul, map_inv, map_mul, ← hyw, inv_mul_cancel]
    exact (S.ρ_eq_one_iff _).mp e
  have e : x = (y₀ : G) * ((w₀ : G) * (((y₀ : G) * w₀)⁻¹ * x)) := by group
  rw [e]
  refine mul_mem (mem_sup_left ⟨L0_le_La S g hy₀L, hy₀N⟩) (mem_sup_right ⟨?_, ?_⟩)
  · exact mul_mem (L0_le_La S _ hw₀L) (QG_le_La S _ hq)
  · exact mul_mem hw₀N (hQN hq)

theorem timmesfeld_6_5_nqHyp : NQHyp S g t := by
  have h1 := pair_one (t := t) hb
  exact nqHyp_of_pair H C ht ht1 hVQ h1.1 hh (hgen 1 h h1.1 hh h1.2) hN0

variable [NQHyp S g t]

include hNo in
theorem fixOf_nqRep_eq {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    {k : S.M} (hk : S.ρ k ∈ Rbar S g t) {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hT : T = LhmodN S g t k) :
    S2.fixOf (nqRep S g t hY) T = nqSub S g t (S.Lbar ((k : G) * g)) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  ext m
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  rw [mem_fixOf_nqRep_iff hY (K := (S.Lbar ((k : G) * g) : Set S.O))
    (fun x hx => Lbar_mul_le_Rbar htk hx) (fun e he => ?_) n, mem_nqSub htk]
  · constructor
    · exact mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb hk n.2
    · intro hn l hl
      rw [Lbar_comm S (H.mul k).conj_mem hl hn, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  · rw [hT, SetLike.mem_coe, ← map_subgroupOf_resV_mul H.conj_mem htk]
    constructor
    · rintro ⟨l, hl, hle⟩
      exact ⟨l, hl, hle.symm⟩
    · rintro ⟨l, hl, hle⟩
      exact ⟨_, hl, hle.symm⟩

include hNo in
theorem isCompl_fixOf_nqRep {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hY : RmodN S g t = Y) {T₁ T₂ : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hT₁ : T₁ = LmodN S g t) (hT₂ : T₂ = LhmodN S g t h) :
    IsCompl (S2.fixOf (nqRep S g t hY) T₁) (S2.fixOf (nqRep S g t hY) T₂) := by
  have h1 := pair_one (t := t) hb
  have hL1 : (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t 1 := by
    ext e
    simp only [SetLike.mem_coe, LmodN, LhmodN, OneMemClass.coe_one, one_mul]
  rw [fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hY h1.1 (hT₁.trans hL1),
    fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hY hh hT₂]
  simp only [OneMemClass.coe_one, one_mul]
  have hgen' := hgen 1 h h1.1 hh h1.2
  have hinf := timmesfeld_6_5_inf H ht h1.1 hh hgen' hN0 C ht1 hVQ
  simp only [OneMemClass.coe_one, one_mul] at hinf
  refine isCompl_nqSub (fun n => ?_) hinf
  obtain ⟨y, hy, w, hw, e⟩ := exists_mul_of_pair H ht h1.1 hh hgen' hN0 n.2
  simp only [OneMemClass.coe_one, one_mul] at hy
  exact ⟨⟨y, hy.2⟩, ⟨w, hw.2⟩, hy.1, hw.1, Subtype.ext e⟩

end Five

theorem timmesfeld_6_5_omega (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (hN0 : Nbar S g t = N0bar S g t) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    [NQHyp S g t] {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) (hE : LmodN S g t = pointRadical Q (aV ht)) :
    S2.RadDecomp (nqRep S g t hX) ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) := by
  have hc := isCompl_fixOf_nqRep H hNo C ht ht1 hVQ
    (pairGen_of_omegaCase H hNo C ht ht1 hVQ hΩ) hN0 hh hb hX
    (T₁ := (pointRadical Q (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)))
    (T₂ := (pointRadical Q (bV (mem_Lbar_of_pair H ht hh)) : Set _)) (by rw [hE])
    (by rw [LhmodN_eq_pointRadical H ht hh (mem_Lbar_of_pair H ht hh) hX hE])
  exact radDecomp_bot_of_isCompl hc

theorem timmesfeld_6_5_sp (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hN0 : Nbar S g t = N0bar S g t) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    [NQHyp S g t] :
    S2.SpRadDecomp (nqRep S g t hSp.eq_sp) ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) := by
  have hth := mem_Lbar_of_pair H ht hh
  set β := beta H C ht ht1 hVQ with hβ
  have hβa := beta_isAlt H C ht ht1 hVQ
  have hLb : LhmodN S g t h = spPointRadical β (bV hth) := by
    set e := resV H.conj_mem t ⟨S.ρ h, hh⟩ with he
    have heR : e ∈ RmodN S g t := by rw [← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
    have hea := resV_aV H.conj_mem ht hh hth
    have heI : e ∈ TauCeti.BilinForm.isometryGroup β := hSp.eq_sp ▸ heR
    rw [LhmodN_eq_map_conj H ht hth heR hea, hSp.LmodN_eq]
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      have := conj_mem_spPointRadical hβa heI hw
      rwa [hea] at this
    · intro w hw
      refine ⟨e⁻¹ * w * e, ?_, by simp [mul_assoc]⟩
      have hb' : e⁻¹ (bV hth) = aV ht := by
        rw [← hea]
        exact LinearEquiv.symm_apply_apply _ _
      have h1 := conj_mem_spPointRadical hβa (inv_mem heI) hw
      rwa [inv_inv, hb'] at h1
  have hc := isCompl_fixOf_nqRep H hNo C ht ht1 hVQ
    (pairGen_of_spCase H C ht ht1 hVQ hSp) hN0 hh hb hSp.eq_sp
    (T₁ := (spPointRadical β (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)))
    (T₂ := (spPointRadical β (bV hth) : Set _)) (by rw [hSp.LmodN_eq]) (by rw [hLb])
  exact spRadDecomp_bot_of_isCompl hc

end CFSG.LargeExtraspecial.S6
