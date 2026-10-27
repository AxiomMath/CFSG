module

public import CFSG.LargeExtraspecial.S6ThreeB
public import CFSG.LargeExtraspecial.S2RadCard
public import CFSG.LargeExtraspecial.S6FiveC
public import CFSG.LargeExtraspecial.S6OneC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_inf_Nbar_eq {t : S.O} [hN : NQHyp S g t] (ht1 : t ≠ 1) (htt : t * t = 1)
    (htN : t ∈ Nbar S g t) {X : Subgroup S.O} (htX : t ∈ X) :
    Nat.card (X ⊓ Nbar S g t : Subgroup S.O) = 2 * 2 ^ finrank (ZMod 2) (nqSub S g t X) := by
  let toN : ↥(X ⊓ Nbar S g t) → ↥(Nbar S g t) := fun x => ⟨x, (Subgroup.mem_inf.mp x.2).2⟩
  set ψ : ↥(X ⊓ Nbar S g t) →* Multiplicative (NQ S g t) :=
    { toFun := fun x => Multiplicative.ofAdd (nqMk (toN x))
      map_one' := rfl
      map_mul' := fun x y => rfl } with hψ
  have hker : Nat.card ψ.ker = 2 := by
    have e : ψ.ker = (zpowers t).subgroupOf (X ⊓ Nbar S g t) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change Multiplicative.ofAdd (nqMk (toN x)) = 1 ↔ _
      rw [← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq, nqMk_eq_zero_iff]
    have hle : zpowers t ≤ X ⊓ Nbar S g t := (zpowers_le).mpr ⟨htX, htN⟩
    rw [e, ← card_map_of_injective (X ⊓ Nbar S g t).subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr hle, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hrange : Nat.card ψ.range = Nat.card (nqSub S g t X) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun m => ?_)
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨toN x, (Subgroup.mem_inf.mp x.2).1, rfl⟩
    · rintro ⟨n, hnX, hn⟩
      exact ⟨⟨n, Subgroup.mem_inf.mpr ⟨hnX, n.2⟩⟩, Multiplicative.toAdd.injective hn⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker] at h1
  have h2 := S2.natCard_submodule (nqSub S g t X)
  omega

theorem self_mem_Nbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) : t ∈ Nbar S g t := by
  refine mem_Nbar.mpr ⟨Lbar_le_Rbar ht ht, fun v hv => ?_⟩
  unfold Vt at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hth, rfl⟩ := hv
    exact S.mem_fixLbar.mp (S.cl_mem_fixLbar_self (H.mul h).conj_mem) t hth
  | zero => exact map_zero _
  | add u w _ _ hu hw => rw [map_add, hu, hw]
  | smul c u _ hu => rw [map_smul, hu]

theorem exists_pair (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    ∃ h : S.M, S.ρ h ∈ Rbar S g t ∧ (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g := by
  have haQ := H.conj_mem
  by_contra hcon
  push Not at hcon
  have hle : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [Vt_eq_span_orbit H ht, Submodule.span_le]
    intro u hu
    obtain ⟨k, hk, rfl⟩ := exists_of_mem_orbit hu haQ
    have hQ := conj_mem_QG' S k.2 haQ
    exact S.cl_mem_clSub (Subgroup.mem_inf.mpr ⟨hQ, hcon k hk⟩) hQ
  have h2 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  rw [inf_eq_right.mpr hle] at h2
  omega

theorem Nbar_eq_N0bar_of_spCase (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) : Nbar S g t = N0bar S g t := by
  rcases Nbar_eq_N0bar_or hCE H C ht (dtEqConj_of_transitive H ht hSp.transitive)
    (naturalPair_of_spCase H hNo C hSp) with h | ⟨hA, -⟩
  · exact h
  · exfalso
    obtain ⟨-, β', hβ', hnd', -, -, hcard, -, -⟩ := hA
    rw [hSp.LmodN_eq, card_spPointRadical hβ' hnd' (aV_ne_zero H ht),
      card_spPointRadical (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
        (aV_ne_zero H ht)] at hcard
    have hpos : 0 < 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) := by positivity
    omega

theorem LhmodN_eq_spPointRadical (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    {h : S.M} (hh : S.ρ h ∈ Rbar S g t) :
    LhmodN S g t h = spPointRadical (beta H C ht ht1 hVQ) (bV (mem_Lbar_of_pair H ht hh)) := by
  have hth := mem_Lbar_of_pair H ht hh
  have hβa := beta_isAlt H C ht ht1 hVQ
  set e := resV H.conj_mem t ⟨S.ρ h, hh⟩ with he
  have heR : e ∈ RmodN S g t := by rw [← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have hea := resV_aV H.conj_mem ht hh hth
  have heI : e ∈ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := hSp.eq_sp ▸ heR
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

section Pair

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : PairGen S g t) (hN0 : Nbar S g t = N0bar S g t) {h : S.M}
  (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) [NQHyp S g t]
include H C ht ht1 hVQ hgen hN0 hh hb

theorem isCompl_nqSub_Lbar :
    IsCompl (nqSub S g t (S.Lbar g)) (nqSub S g t (S.Lbar ((h : G) * g))) := by
  have h1 := pair_one (t := t) hb
  have hgen' := hgen 1 h h1.1 hh h1.2
  have hinf := timmesfeld_6_5_inf H ht h1.1 hh hgen' hN0 C ht1 hVQ
  simp only [OneMemClass.coe_one, one_mul] at hinf
  refine isCompl_nqSub (fun n => ?_) hinf
  obtain ⟨y, hy, w, hw, e⟩ := exists_mul_of_pair H ht h1.1 hh hgen' hN0 n.2
  simp only [OneMemClass.coe_one, one_mul] at hy
  exact ⟨⟨y, hy.2⟩, ⟨w, hw.2⟩, hy.1, hw.1, Subtype.ext e⟩

theorem finrank_NQ_eq :
    finrank (ZMod 2) (NQ S g t) = 2 * finrank (ZMod 2) (nqSub S g t (S.Lbar g)) := by
  have hth := mem_Lbar_of_pair H ht hh
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  have h1 := Submodule.finrank_add_eq_of_isCompl
    (isCompl_nqSub_Lbar H C ht ht1 hVQ hgen hN0 hh hb)
  have h2 := card_inf_Nbar_eq ht1 htt (self_mem_Nbar H ht) ht
  have h3 := card_inf_Nbar_eq ht1 htt (self_mem_Nbar H ht) hth
  rw [card_Lbar_mul_inf_Nbar H hh, h2] at h3
  have := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h3)
  omega

end Pair

theorem odd_width_sp (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) : Odd S.width := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have hdvd := S2.sp_timmesfeld_2_1_b_dvd (nqRep S g t hSp.eq_sp) (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) m (bot_inf_eq _) (by omega)
    (by rw [S2.spPerp_bot, finrank_top]; omega) (fun _ _ v _ => Submodule.mem_top)
    (by rw [S2.spPerp_bot]; exact Submodule.mem_top)
    (by rw [S2.spPerp_bot]; exact Submodule.mem_top) (beta_aV_bV H C ht ht1 hVQ hh hb) hD
  rw [finrank_top, finrank_NQ_eq H C ht ht1 hVQ hgen hN0 hh hb] at hdvd
  have hcard := card_inf_Nbar_eq ht1 (mul_self_of_mem_Lbar S H.conj_mem ht) (self_mem_Nbar H ht) ht
  rw [card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp, ← pow_succ'] at hcard
  have he := Nat.pow_right_injective le_rfl hcard
  have hw := finrank_Vt_le_width H ht1
  have h4m : 4 ∣ 2 ^ m := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [hk, pow_add]
    exact Dvd.intro_left _ rfl
  obtain ⟨c, hc⟩ := h4m.trans hdvd
  refine ⟨S.width / 2, ?_⟩
  omega

end CFSG.LargeExtraspecial.S6
