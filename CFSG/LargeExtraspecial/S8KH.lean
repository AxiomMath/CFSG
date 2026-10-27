module

public import CFSG.LargeExtraspecial.S8KG
public import CFSG.LargeExtraspecial.S8KA
public import CFSG.LargeExtraspecial.S8KE
public import CFSG.LargeExtraspecial.S9GenE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem nqSub_mono [NQHyp S g t] {X Y : Subgroup S.O} (h : X ≤ Y) :
    nqSub S g t X ≤ nqSub S g t Y :=
  fun _ ⟨n, hn, e⟩ => ⟨n, h hn, e⟩

theorem exists_mem_Fbar_not_mem_zpowers [NQHyp S g t]
    (hpos : 0 < finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t))) :
    ∃ f ∈ S9.Fbar S g t, f ∉ zpowers t := by
  have hne : nqSub S g t (S9.Fbar S g t) ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hnF, rfl⟩ := hm
  exact ⟨n, hnF, fun h => hm0 ((nqMk_eq_zero_iff _).mpr h)⟩

theorem nqSub_Fbar_eq_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (hτK : τ ∈ CMt S t) :
    nqSub S g t (S9.Fbar S g t) = (nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩) := by
  have hFN := conjL_subset_Nbar hsub
  have hkey := hkey_of_hsub D hsub
  have hle : (nqSub S g t (S.Lbar g)).map (nqComm S g t ⟨τ, hτK⟩) ≤
      nqSub S g t (S9.Fbar S g t) := by
    rintro _ ⟨m, ⟨n, hnL, rfl⟩, rfl⟩
    have hc := comm_mem_Fbar_of_mem_Abar hCE hNo hΩ D (Or.inr hm4) hsub hxM hxτ hτt hτV hτN
      (fun h => by omega) ⟨hnL, n.2⟩
    have hcN := S9.Fbar_le_of_subset hFN hc
    exact ⟨⟨_, hcN⟩, hc, (nqComm_mk ⟨τ, hτK⟩ n hcN).symm⟩
  have h4 := finrank_map_nqComm_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK
  have hge := Submodule.finrank_mono hle
  rw [h4] at hge
  have hle4 : finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t)) ≤ 4 := by
    by_contra hlt
    push Not at hlt
    rcases S9.fix_or_prod_dvd_card H C ht hFN hkey (by omega) with hall | hdvd
    · obtain ⟨f, hf, hft⟩ := exists_mem_Fbar_not_mem_zpowers
        (by omega : 0 < finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t)))
      obtain ⟨r, hr, f', hf', hrf⟩ := exists_move_Fbar hNo hΩ D (by omega) hFN hf hft
      exact hrf (hall r hr f' hf')
    · apply not_thirtyone_dvd_card_Rbar H ht D.hX (by rw [D.hdim, hm4])
      refine dvd_trans ?_ (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
      have h5 : 4 ∈ Finset.range (finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t))) :=
        Finset.mem_range.mpr (by omega)
      exact Finset.dvd_prod_of_mem (fun i => 2 ^ (i + 1) - 1) h5
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

theorem finrank_nqSub_Fbar_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] : finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t)) = 4 := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hτK : τ ∈ CMt S t := mem_CMt.mpr ⟨hτM, hτt⟩
  rw [nqSub_Fbar_eq_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK]
  exact finrank_map_nqComm_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK

theorem Rbar_inf_le_GamF (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    Rbar S g t ⊓ normalizer (S9.Fbar S g t : Set S.O) ≤ S9.GamF S g t := fun _ hx =>
  S9.mem_GamF.mpr ⟨⟨Rbar_le_Mbar hx.1, commute_of_mem_Rbar haQ hx.1⟩, hx.2⟩

theorem normal_Rbar_inf_GamF :
    ((Rbar S g t ⊓ normalizer (S9.Fbar S g t : Set S.O)).subgroupOf (S9.GamF S g t)).Normal := by
  constructor
  intro x hx γ
  rw [mem_subgroupOf] at hx ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨⟨hγM, hγt⟩, hγF⟩ := S9.mem_GamF.mp γ.2
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hγM
  refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hγF hx.2) (inv_mem hγF)⟩
  have := conj_mem_Rbar (k := k) (by rw [hk]; exact hγt) hx.1
  rw [hk] at this
  exact this

theorem forall_actsTv_Fbar_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (c : nqSub S g t (S9.Fbar S g t))
    (μ : Dual (ZMod 2) (nqSub S g t (S9.Fbar S g t))) (hμ : μ c = 0) :
    ∃ δ ∈ (Rbar S g t ⊓ normalizer (S9.Fbar S g t : Set S.O)).subgroupOf (S9.GamF S g t),
      S9.ActsTv (S9.fqHom S g t) δ c μ := by
  have haQ := H.conj_mem
  have hFN := conjL_subset_Nbar hsub
  have hkey := hkey_of_hsub D hsub
  have hF4 := finrank_nqSub_Fbar_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN
  have hT := S9.forall_actsTv_of_exists (ρ := S9.fqHom S g t)
    (fun c v hc hv => S9.exists_fqHom_actsTv H C ht hFN hkey hc hv)
  have hRG := Rbar_inf_le_GamF haQ (t := t)
  obtain ⟨f, hf, hft⟩ := exists_mem_Fbar_not_mem_zpowers
    (by omega : 0 < finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t)))
  obtain ⟨r, hr, f', hf', hrf⟩ := exists_move_Fbar hNo hΩ D (by omega) hFN hf hft
  have hδ₀ : (⟨r, hRG hr⟩ : S9.GamF S g t) ∈
      (Rbar S g t ⊓ normalizer (S9.Fbar S g t : Set S.O)).subgroupOf (S9.GamF S g t) := by
    rw [mem_subgroupOf]
    exact hr
  have hf'N : f' ∈ Nbar S g t := S9.Fbar_le_of_subset hFN hf'
  have hrf'N : r * f' * r⁻¹ ∈ Nbar S g t :=
    S9.Fbar_le_of_subset hFN ((mem_normalizer_iff.mp hr.2 _).mp hf')
  have hv₀ : S9.fqHom S g t ⟨r, hRG hr⟩ ⟨nqMk ⟨f', hf'N⟩, ⟨⟨f', hf'N⟩, hf', rfl⟩⟩ ≠
      ⟨nqMk ⟨f', hf'N⟩, ⟨⟨f', hf'N⟩, hf', rfl⟩⟩ := by
    intro he
    apply hrf
    have h1 := congrArg Subtype.val he
    rw [S9.coe_fqHom_apply _ _ hf' rfl (x' := ⟨_, hrf'N⟩) rfl, nqMk_eq_iff] at h1
    exact h1
  exact S9.forall_actsTv_of_normal hT normal_Rbar_inf_GamF (by rw [hF4]; norm_num) hδ₀ hv₀
    c μ hμ

theorem nqHom_mem_range_nqComm (H : Hyp4 S g) [NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) {τ : S.O}
    (hτK : τ ∈ CMt S t) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (r : Rbar S g t) {v : NQ S g t} (hv : v ∈ LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) :
    nqHom S g t r v ∈ LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
  have heY : resV H.conj_mem t r ∈ Y := by
    rw [← hY, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  have h1 := nqComm_mem_range hY ⟨τ, hτK⟩ (comm_mem_Nbar_of_fix' H hτK hτV) ⟨_, heY⟩ hv
  rwa [nqRep_eq hY (x := r) rfl] at h1

theorem nqSub_Lbar_inf_nqSub_Lbar_mul_eq_bot (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) [NQHyp S g t] :
    nqSub S g t (S.Lbar g) ⊓ nqSub S g t (S.Lbar ((D.h : G) * g)) = ⊥ := by
  have hD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have hT : ((S2.radFix D.Q ⊥ (bV (mem_Lbar_of_pair H ht D.hh)) : Subgroup _) :
      Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t D.h := by
    rw [S2.radFix_bot, LhmodN_eq_pointRadical H ht D.hh (mem_Lbar_of_pair H ht D.hh) D.hX D.hE]
  have hB := fixOf_nqRep_eq H hNo C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb D.hX D.hh hT
  have h2 := hD.2
  rw [top_inf_eq, top_inf_eq, fixOf_nqRep_radFix_eq hNo D, hB] at h2
  exact h2

theorem nqHom_mem_nqSub_Lbar_mul [NQHyp S g t] {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    {v : NQ S g t} (hv : v ∈ nqSub S g t (S9.Fbar S g t)) :
    nqHom S g t ⟨S.ρ h, hh⟩ v ∈ nqSub S g t (S.Lbar ((h : G) * g)) := by
  obtain ⟨n, hnF, rfl⟩ := hv
  rw [nqHom_mk]
  refine ⟨_, ?_, rfl⟩
  rw [coe_nConj, Lbar_mul S h g]
  exact ⟨n, S9.Fbar_le_Lbar hnF, rfl⟩

theorem map_nqHom_le_nqSub_Lbar_mul [NQHyp S g t] {h : S.M} (hh : S.ρ h ∈ Rbar S g t) :
    (nqSub S g t (S9.Fbar S g t)).map
        (nqHom S g t ⟨S.ρ h, hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) ≤
      nqSub S g t (S.Lbar ((h : G) * g)) :=
  Submodule.map_le_iff_le_comap.mpr fun _ hw => nqHom_mem_nqSub_Lbar_mul hh hw

theorem range_nqComm_eq_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    [NQHyp S g t] (hτK : τ ∈ CMt S t) :
    LinearMap.range (nqComm S g t ⟨τ, hτK⟩) = nqSub S g t (S9.Fbar S g t) ⊔
      (nqSub S g t (S9.Fbar S g t)).map
        (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) := by
  have hF := nqSub_Fbar_eq_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK
  have hF4 := finrank_nqSub_Fbar_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN
  have hFr : nqSub S g t (S9.Fbar S g t) ≤ LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
    rw [hF]
    exact LinearMap.map_le_range
  have hle : nqSub S g t (S9.Fbar S g t) ⊔ (nqSub S g t (S9.Fbar S g t)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) ≤
        LinearMap.range (nqComm S g t ⟨τ, hτK⟩) := by
    refine sup_le hFr (Submodule.map_le_iff_le_comap.mpr fun v hv => ?_)
    exact nqHom_mem_range_nqComm H D.hX hτK hτV _ (hFr hv)
  have htwo := (finrank_range_nqComm hNo hΩ D hτK hτV).2
  have h4 := finrank_map_nqComm_of_four hCE hNo hΩ D hm4 hsub hxM hxτ hτt hτV hτN hτK
  rw [h4] at htwo
  have hmap : finrank (ZMod 2) ((nqSub S g t (S9.Fbar S g t)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t)) = 4 := by
    rw [LinearEquiv.finrank_map_eq, hF4]
  have hinf : nqSub S g t (S9.Fbar S g t) ⊓ (nqSub S g t (S9.Fbar S g t)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    have hvA : v ∈ nqSub S g t (S.Lbar g) := nqSub_mono S9.Fbar_le_Lbar hv.1
    have hvB : v ∈ nqSub S g t (S.Lbar ((D.h : G) * g)) := map_nqHom_le_nqSub_Lbar_mul D.hh hv.2
    exact eq_bot_iff.mp (nqSub_Lbar_inf_nqSub_Lbar_mul_eq_bot hNo hΩ D) ⟨hvA, hvB⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (nqSub S g t (S9.Fbar S g t))
    ((nqSub S g t (S9.Fbar S g t)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t))
  have h0 := Submodule.finrank_eq_zero.mpr hinf
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

theorem nqSub_N1bar (H : Hyp4 S g) [NQHyp S g t] {σ : S.O} (hσK : σ ∈ CMt S t)
    (hle : N1bar S g t σ ≤ Nbar S g t) :
    nqSub S g t (N1bar S g t σ) = LinearMap.range (nqComm S g t ⟨σ, hσK⟩) := by
  have hσM := (mem_CMt.mp hσK).1
  have hσt := (mem_CMt.mp hσK).2
  have hcN : ∀ n ∈ Nbar S g t, n * σ * n⁻¹ * σ⁻¹ ∈ Nbar S g t := fun n hn => by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hσM
    have h1 := conj_mem_Nbar H.conj_mem (k := k) (by rw [hk]; exact hσt) (inv_mem hn)
    rw [hk] at h1
    rw [show n * σ * n⁻¹ * σ⁻¹ = n * (σ * n⁻¹ * σ⁻¹) by group]
    exact mul_mem hn h1
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact nqMk_mem_range_of_mem_N1bar H hσK hle hn n.2
  · rintro _ ⟨m, rfl⟩
    obtain ⟨n, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) m
    exact ⟨⟨_, hcN _ n.2⟩, comm_mem_N1bar n.2, (nqComm_mk ⟨σ, hσK⟩ n (hcN _ n.2)).symm⟩

theorem eq_of_nqSub_eq [NQHyp S g t] {X Y : Subgroup S.O} (hX : X ≤ Nbar S g t)
    (hY : Y ≤ Nbar S g t) (htX : t ∈ X) (htY : t ∈ Y) (h : nqSub S g t X = nqSub S g t Y) :
    X = Y := by
  ext x
  constructor
  · intro hx
    have h1 := (mem_nqSub htX ⟨x, hX hx⟩).mpr hx
    rw [h] at h1
    exact (mem_nqSub htY ⟨x, hX hx⟩).mp h1
  · intro hx
    have h1 := (mem_nqSub htY ⟨x, hY hx⟩).mpr hx
    rw [← h] at h1
    exact (mem_nqSub htX ⟨x, hY hx⟩).mp h1

end CFSG.LargeExtraspecial.S8
