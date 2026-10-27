module

public import CFSG.LargeExtraspecial.S9RATri
public import CFSG.LargeExtraspecial.S9RAAbs
public import CFSG.LargeExtraspecial.S9GenD
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S9RALevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Gen

variable {t : S.O} [hN : NQHyp S g t]

theorem nqMk_inv (n : Nbar S g t) : nqMk n⁻¹ = nqMk n :=
  (nqMk_eq_iff _ _).mpr (by simpa using hN.sq n n.2)

theorem nqMk_comm_eq (σ : S8.CMt S t) (n : Nbar S g t) :
    nqMk (n * nConjC σ n⁻¹) = nqLinC σ (nqMk n) + nqMk n := by
  rw [nqMk_mul, ← nqLinC_mk]
  simp only [nqMk_inv]
  exact add_comm _ _

theorem nqRep_nqLinC_comm {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    (σ : S8.CMt S t) (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    (e : Y) (m : NQ S g t) : nqRep S g t hY e (nqLinC σ m) = nqLinC σ (nqRep S g t hY e m) := by
  have hm := nqMk_surjective m
  obtain ⟨n, hn⟩ := hm
  subst hn
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hY]
    exact e.2
  rw [← range_resV hN.conj_mem t] at heR
  obtain ⟨r, hr⟩ := heR
  simp only [nqRep_apply hY hr.symm, nqLinC_mk]
  rw [nqMk_eq_iff]
  simp only [coe_nConjC, coe_nConj]
  have hc := hσR r r.2
  have hy := (nConj r (nConjC σ n)).2
  simp only [coe_nConj, coe_nConjC] at hy
  convert hN.comm _ (inv_mem hy) _ hc using 1
  group

theorem nqRep_mem_range {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    (σ : S8.CMt S t) (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    (e : Y) {u : NQ S g t} (hu : u ∈ LinearMap.range (nqLinC σ + LinearMap.id)) :
    nqRep S g t hY e u ∈ LinearMap.range (nqLinC σ + LinearMap.id) := by
  obtain ⟨m, rfl⟩ := hu
  exact ⟨nqRep S g t hY e m, by
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_add, nqRep_nqLinC_comm hY σ hσR]⟩

theorem comm_mem_zpowers_of_range_eq_bot (σ : S8.CMt S t)
    (h : LinearMap.range (nqLinC (g := g) σ + LinearMap.id) = ⊥) (n : Nbar S g t) :
    (σ : S.O) * n * (σ : S.O)⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := by
  have hm : (nqLinC σ + LinearMap.id : NQ S g t →ₗ[ZMod 2] NQ S g t) (nqMk n) ∈
      LinearMap.range (nqLinC (g := g) σ + LinearMap.id) := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, LinearMap.add_apply, LinearMap.id_apply, nqLinC_mk, ← nqMk_mul,
    nqMk_eq_zero_iff] at hm
  simp only [Subgroup.coe_mul, coe_nConjC] at hm
  have h2 := mul_mem hm (hN.sq _ (inv_mem n.2))
  convert h2 using 1
  group

theorem card_range_le_card_nOrbit (σ : S8.CMt S t) :
    Nat.card (LinearMap.range (nqLinC (g := g) σ + LinearMap.id)) ≤
      Nat.card (nOrbit (Nbar S g t) (σ : S.O)) := by
  have hmem : ∀ ρ ∈ nOrbit (Nbar S g t) (σ : S.O), ρ * (σ : S.O)⁻¹ ∈ Nbar S g t := by
    rintro ρ ⟨n, hn, rfl⟩
    have h1 := (nConjC σ ⟨n⁻¹, inv_mem hn⟩).2
    rw [coe_nConjC] at h1
    convert mul_mem hn h1 using 1
    group
  have hval : ∀ n : Nbar S g t,
      nqMk ⟨(n : S.O) * (σ : S.O) * (n : S.O)⁻¹ * (σ : S.O)⁻¹, hmem _ ⟨n, n.2, rfl⟩⟩ =
        (nqLinC σ + LinearMap.id : NQ S g t →ₗ[ZMod 2] NQ S g t) (nqMk n) := by
    intro n
    have e : (⟨(n : S.O) * (σ : S.O) * (n : S.O)⁻¹ * (σ : S.O)⁻¹, hmem _ ⟨n, n.2, rfl⟩⟩ :
        Nbar S g t) = n * nConjC σ n⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, coe_nConjC, Subgroup.coe_inv]
      group)
    exact (congrArg nqMk e).trans (nqMk_comm_eq σ n)
  have hrange : ∀ ρ (hρ : ρ ∈ nOrbit (Nbar S g t) (σ : S.O)),
      nqMk ⟨ρ * (σ : S.O)⁻¹, hmem ρ hρ⟩ ∈ LinearMap.range (nqLinC (g := g) σ + LinearMap.id) := by
    rintro ρ ⟨n, hn, rfl⟩
    exact ⟨nqMk ⟨n, hn⟩, (hval ⟨n, hn⟩).symm⟩
  refine Nat.card_le_card_of_surjective (fun ρ => ⟨nqMk ⟨ρ.1 * (σ : S.O)⁻¹, hmem ρ.1 ρ.2⟩,
    hrange ρ.1 ρ.2⟩) ?_
  rintro ⟨u, m, hmu⟩
  have hm := nqMk_surjective m
  obtain ⟨n, hn⟩ := hm
  subst hn
  refine ⟨⟨_, n, n.2, rfl⟩, Subtype.ext ?_⟩
  change nqMk ⟨(n : S.O) * (σ : S.O) * (n : S.O)⁻¹ * (σ : S.O)⁻¹, hmem _ ⟨n, n.2, rfl⟩⟩ = u
  exact (hval n).trans hmu

theorem nqLinC_nqLinC_of_mul_self (σ : S8.CMt S t) (hσ : σ * σ = 1) (u : NQ S g t) :
    nqLinC σ (nqLinC σ u) = u := by
  rw [nqLinC_comp, hσ, nqLinC_one]

theorem nqRep_nqRep_of_mul_self {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hY : RmodN S g t = Y) (e : Y) (he : e * e = 1) (u : NQ S g t) :
    nqRep S g t hY e (nqRep S g t hY e u) = u := by
  have h2 : nqRep S g t hY (e * e) u = u := by rw [he, map_one]; rfl
  exact (congrArg (fun φ : NQ S g t ≃ₗ[ZMod 2] NQ S g t => φ u)
    (map_mul (nqRep S g t hY) e e)).symm.trans h2

theorem nqLinC_mem_nqSub (σ : S8.CMt S t) {X : Subgroup S.O}
    (hσX : ∀ x ∈ X, (σ : S.O) * x * (σ : S.O)⁻¹ ∈ X) {u : NQ S g t} (hu : u ∈ nqSub S g t X) :
    nqLinC σ u ∈ nqSub S g t X := by
  obtain ⟨n, hn, rfl⟩ := hu
  exact ⟨nConjC σ n, by rw [coe_nConjC]; exact hσX n hn, rfl⟩

theorem nqLinC_eq_of_levi {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    (σ : S8.CMt S t) (hσσ : σ * σ = 1)
    (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    {U : Submodule (ZMod 2) (NQ S g t)} (hU2 : finrank (ZMod 2) U = 2)
    (hσU : ∀ u ∈ U, nqLinC σ u ∈ U) (ex ey : Y) (hexx : ex * ex = 1) (heyy : ey * ey = 1)
    (hexU : ∀ u ∈ U, nqRep S g t hY ex u ∈ U) (heyU : ∀ u ∈ U, nqRep S g t hY ey u ∈ U)
    (hlevi : ∀ u ∈ U, nqRep S g t hY ex u = u → nqRep S g t hY ey u = u → u = 0) :
    ∀ u ∈ U, nqLinC σ u = u :=
  eq_of_commute_levi hU2 (fun u => nqRep S g t hY ex u) (fun u => nqRep S g t hY ey u)
    (nqLinC σ) (map_zero _) (map_zero _) hexU heyU hσU
    (fun u _ => nqRep_nqRep_of_mul_self hY ex hexx u)
    (fun u _ => nqRep_nqRep_of_mul_self hY ey heyy u)
    (fun u _ => nqLinC_nqLinC_of_mul_self σ hσσ u)
    (fun u _ => (nqRep_nqLinC_comm hY σ hσR ex u).symm)
    (fun u _ => (nqRep_nqLinC_comm hY σ hσR ey u).symm) hlevi

theorem commute_of_nqLinC_eq (htt : t * t = 1) (σ : S8.CMt S t)
    (hσ : ∀ y : S.O, y * σ * y⁻¹ ≠ (σ : S.O) * t) (n : Nbar S g t)
    (h : nqLinC σ (nqMk n) = nqMk n) : (σ : S.O) * n = n * σ := by
  rw [nqLinC_mk, nqMk_eq_iff, coe_nConjC] at h
  have hσt : (σ : S.O) * t = t * σ := (S8.mem_CMt.mp σ.2).2
  rcases S8.eq_one_or_eq_of_mem_zpowers htt h with h1 | h1
  · have e := inv_mul_eq_one.mp h1
    calc (σ : S.O) * n = (σ * n * (σ : S.O)⁻¹) * σ := by group
      _ = n * σ := by rw [e]
  · exfalso
    apply hσ (n : S.O)⁻¹
    have e : (n : S.O)⁻¹ * σ * (n : S.O)⁻¹⁻¹ = (((σ : S.O) * n * (σ : S.O)⁻¹)⁻¹ * n)⁻¹ * σ := by
      group
    rw [e, h1, inv_eq_of_mul_eq_one_right htt, hσt]

end Gen

section NQ

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem not_forall_commute_Nbar (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    ¬ ∀ n ∈ Nbar S g t, x * t * x⁻¹ * n = n * (x * t * x⁻¹) := by
  intro hcomm
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hbot := commSpace_inf_Vone_eq_bot hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hτt hβ
  have hint : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ⊓
      commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨-, huV⟩, huC⟩
    have : u ∈ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        Vone S g t g ((h : G) * g) := ⟨huC, huV⟩
    rwa [hbot] at this
  have hτP := fix_clSub_of_commute_Abar hCE H hNo C ht ht1 hVQ hSp hh hb hτM hτa
    (fun β hβA => hcomm β hβA.2) hint
  have hτL := commute_Lbar_of_fix_clSub H C hτM hτa hτP
  have hmemL := mem_Lbar_of_commute H C ht hxM hτL
  have hmemN := hL x hxM hmemL
  refine hβ 1 (by rw [map_one]; exact one_mem _) ⟨?_, hmemN⟩
  simpa using hmemL

theorem sixteen_le_card_nOrbit (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    16 ≤ Nat.card (nOrbit (Nbar S g t) (x * t * x⁻¹)) := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hNQ : NQHyp S g t :=
    timmesfeld_6_5_nqHyp H C ht ht1 hVQ (pairGen_of_spCase H C ht ht1 hVQ hSp) hN0 hh hb
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have hτK : x * t * x⁻¹ ∈ S8.CMt S t := S8.mem_CMt.mpr ⟨hτM, hτt⟩
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  have hσR : ∀ r ∈ Rbar S g t, ((⟨_, hτK⟩ : S8.CMt S t) : S.O) * r *
      ((⟨_, hτK⟩ : S8.CMt S t) : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t := fun r hr =>
    comm_mem_Nbar_of_fix haQ hτM hτt hτV hr
  have hdvd := pow_dvd_finrank_of_invariant (nqRep S g t hSp.eq_sp) (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (m := 2) (by norm_num) (by rw [h4])
    (beta_aV_bV H C ht ht1 hVQ hh hb) hD
    (fun e u hu => nqRep_mem_range hSp.eq_sp (⟨_, hτK⟩ : S8.CMt S t) hσR e hu)
  have hU0 : LinearMap.range (nqLinC (g := g) (⟨_, hτK⟩ : S8.CMt S t) + LinearMap.id) ≠ ⊥ := by
    intro hbot
    apply not_forall_commute_Nbar hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hτt hβ
    intro n hn
    have h1 := comm_mem_zpowers_of_range_eq_bot _ hbot ⟨n, hn⟩
    rcases S8.eq_one_or_eq_of_mem_zpowers htt h1 with h2 | h2
    · calc x * t * x⁻¹ * n = (x * t * x⁻¹ * n * (x * t * x⁻¹)⁻¹ * n⁻¹) * n * (x * t * x⁻¹) := by
            group
        _ = n * (x * t * x⁻¹) := by
            rw [show x * t * x⁻¹ * n * (x * t * x⁻¹)⁻¹ * n⁻¹ = 1 from h2, one_mul]
    · exfalso
      have h2' : x * t * x⁻¹ * n * (x * t * x⁻¹)⁻¹ * n⁻¹ = t := h2
      have h3 : n * (x * t * x⁻¹) * n⁻¹ * (x * t * x⁻¹)⁻¹ = t⁻¹ :=
        calc n * (x * t * x⁻¹) * n⁻¹ * (x * t * x⁻¹)⁻¹ =
            (x * t * x⁻¹ * n * (x * t * x⁻¹)⁻¹ * n⁻¹)⁻¹ := by group
          _ = t⁻¹ := by rw [h2']
      refine not_conj_mul_t_of_inf_eq_bot H C ht ht1 hVQ hinf hτV (y := n) ?_
      calc n * (x * t * x⁻¹) * n⁻¹ = (n * (x * t * x⁻¹) * n⁻¹ * (x * t * x⁻¹)⁻¹) *
            (x * t * x⁻¹) := by group
        _ = t * (x * t * x⁻¹) := by rw [h3, inv_eq_of_mul_eq_one_right htt]
        _ = x * t * x⁻¹ * t := hτt.symm
  have hpos : 0 < finrank (ZMod 2)
      (LinearMap.range (nqLinC (g := g) (⟨_, hτK⟩ : S8.CMt S t) + LinearMap.id)) :=
    Nat.pos_of_ne_zero fun h0 => hU0 (Submodule.finrank_eq_zero.mp h0)
  have hcardU : 16 ≤ Nat.card
      (LinearMap.range (nqLinC (g := g) (⟨_, hτK⟩ : S8.CMt S t) + LinearMap.id)) := by
    rw [← FiniteField.pow_finrank_eq_natCard 2]
    obtain ⟨k, hk⟩ := hdvd
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2)
          (LinearMap.range (nqLinC (g := g) (⟨_, hτK⟩ : S8.CMt S t) + LinearMap.id)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  exact hcardU.trans (card_range_le_card_nOrbit (⟨_, hτK⟩ : S8.CMt S t))

end NQ

end CFSG.LargeExtraspecial.S9
