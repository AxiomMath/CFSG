module

public import CFSG.LargeExtraspecial.S6TwoD
public import CFSG.LargeExtraspecial.S8DimA
public import CFSG.LargeExtraspecial.S8FiveC
public import CFSG.LargeExtraspecial.S8Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem Std.exists_resV_eq (D : Std H C ht ht1 hVQ) (e : omegaGroup D.Q D.hQ) :
    ∃ x : Rbar S g t, (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x := by
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by rw [D.hX]; exact e.2
  rw [← range_resV H.conj_mem t] at heR
  obtain ⟨x, hx⟩ := heR
  exact ⟨x, hx.symm⟩

theorem exists_secMk_eq (v : ↥((Wt S g t).map (Vt S g t).mkQ)) :
    ∃ w, ∃ hw : w ∈ Wt S g t, v = secMk (Vt S g t) hw := by
  obtain ⟨w, hw, hwv⟩ := v.2
  exact ⟨w, hw, Subtype.ext hwv.symm⟩

section Rep

variable (D : Std H C ht ht1 hVQ)
  {ρ : omegaGroup D.Q D.hQ →* (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2]
    ↥((Wt S g t).map (Vt S g t).mkQ))}
  (hρ : ∀ (e : omegaGroup D.Q D.hQ) (x : Rbar S g t),
    (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
    ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
      ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
        (Vt S g t).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
include hρ

theorem secMk_mem_fixOf_LmodN_iff (hNo : NoA2 S g) {w : S.Qt} (hw : w ∈ Wt S g t) :
    secMk (Vt S g t) hw ∈ fixOf ρ (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) ↔
      w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t := by
  have haQ := H.conj_mem
  have hPI := pairInt_of_radBound H C ht ht1 hVQ D.hR
  rw [mem_fixOf, ← forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ D.hh D.hb hPI hw]
  constructor
  · intro hf l hl
    have heL : resV haQ t ⟨l, Lbar_le_Rbar ht hl⟩ ∈ omegaGroup D.Q D.hQ := by
      rw [← D.hX, ← range_resV haQ t]; exact ⟨_, rfl⟩
    have heP : ((⟨_, heL⟩ : omegaGroup D.Q D.hQ) : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
        (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) :=
      ⟨l, hl, fun v => rfl⟩
    have h := congrArg Subtype.val (hf ⟨_, heL⟩ heP)
    rw [hρ ⟨_, heL⟩ ⟨l, Lbar_le_Rbar ht hl⟩ rfl w hw, coe_secMk] at h
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change (Vt S g t).mkQ _ - (Vt S g t).mkQ w = 0
    rw [h, sub_self]
  · intro hf e he
    obtain ⟨x, hx⟩ := D.exists_resV_eq e
    obtain ⟨l, hl, hel⟩ := he
    apply Subtype.ext
    rw [hρ e x hx w hw, coe_secMk]
    have hagree : ∀ v ∈ Vt S g t,
        ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      intro v hv
      have h1 := hel ⟨v, hv⟩
      rw [hx, coe_resV_apply] at h1
      exact h1
    have hxlN : (x : S.O) * l⁻¹ ∈ Nbar S g t := by
      refine mem_Nbar.mpr ⟨mul_mem x.2 (inv_mem (Lbar_le_Rbar ht hl)), fun v hv => ?_⟩
      have hv' := apply_mem_Vt_of_mem_Rbar haQ (inv_mem (Lbar_le_Rbar ht hl)) hv
      rw [coe_mul_apply, hagree _ hv', apply_inv_apply_O]
    have h1 := D.hN _ hxlN _ (apply_mem_Wt H (Lbar_le_Rbar ht hl) hw)
    rw [coe_mul_apply, inv_apply_apply_O] at h1
    have h2 := hf l hl
    have e : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
        (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
          ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
    have hxl : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
      rw [e]
      exact (Vt S g t).add_mem h1 h2
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hxl

theorem finrank_inf_fixOf_LmodN (hNo : NoA2 S g) {U : Submodule (ZMod 2) S.Qt}
    (hVU : Vt S g t ≤ U) (hUW : U ≤ Wt S g t) :
    finrank (ZMod 2) ↥((U.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype ⊓
      fixOf ρ (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t))) =
      finrank (ZMod 2) ((U ⊓ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t)).map
        (Vt S g t).mkQ) := by
  set X := S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t with hX
  have hUXM : (U ⊓ X).map (Vt S g t).mkQ ≤ (Wt S g t).map (Vt S g t).mkQ :=
    Submodule.map_mono (inf_le_left.trans hUW)
  have hinf : (U.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype ⊓
      fixOf ρ (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      ((U ⊓ X).map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype := by
    ext v
    obtain ⟨w, hw, rfl⟩ := exists_secMk_eq v
    rw [Submodule.mem_inf, secMk_mem_fixOf_LmodN_iff D hρ hNo hw, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.coe_subtype, coe_secMk]
    constructor
    · rintro ⟨⟨u, hu, huw⟩, hwX⟩
      have hwU : w ∈ U := by
        have hd : w - u ∈ Vt S g t := by
          rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
          change (Vt S g t).mkQ w - (Vt S g t).mkQ u = 0
          rw [huw, sub_self]
        have h1 := U.add_mem hu (hVU hd)
        rwa [show u + (w - u) = w by abel] at h1
      exact ⟨w, ⟨hwU, hwX⟩, rfl⟩
    · rintro ⟨u, ⟨huU, huX⟩, huw⟩
      refine ⟨⟨u, huU, huw⟩, ?_⟩
      have hd : w - u ∈ Vt S g t := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        change (Vt S g t).mkQ w - (Vt S g t).mkQ u = 0
        rw [huw, sub_self]
      have h1 := X.add_mem huX ((le_sup_right : Vt S g t ≤ X) hd)
      rwa [show u + (w - u) = w by abel] at h1
  rw [hinf]
  exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hUXM)

theorem map_mkQ_invariant {U : Submodule (ZMod 2) S.Qt} (hUW : U ≤ Wt S g t)
    (hU : ∀ r ∈ Rbar S g t, ∀ u ∈ U, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U)
    (e : omegaGroup D.Q D.hQ) :
    ∀ v ∈ (U.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype,
      ρ e v ∈ (U.map (Vt S g t).mkQ).comap ((Wt S g t).map (Vt S g t).mkQ).subtype := by
  intro v hv
  obtain ⟨x, hx⟩ := D.exists_resV_eq e
  obtain ⟨u, huU, huv⟩ := hv
  have huW := hUW huU
  have hv' : v = secMk (Vt S g t) huW := Subtype.ext huv.symm
  rw [hv']
  change ((ρ e (secMk (Vt S g t) huW) : ↥((Wt S g t).map (Vt S g t).mkQ)) :
    S.Qt ⧸ Vt S g t) ∈ U.map (Vt S g t).mkQ
  rw [hρ e x hx u huW]
  exact ⟨_, hU x x.2 u huU, rfl⟩

end Rep

theorem finrank_map_mkQ_of_invariant (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {U : Submodule (ZMod 2) S.Qt}
    (hVU : Vt S g t ≤ U) (hUW : U ≤ Wt S g t)
    (hU : ∀ r ∈ Rbar S g t, ∀ u ∈ U, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) :
    2 ^ (D.m - 1) ∣ finrank (ZMod 2) (U.map (Vt S g t).mkQ) ∧
      (D.IsMinus → 2 ^ D.m ∣ finrank (ZMod 2) (U.map (Vt S g t).mkQ)) ∧
      finrank (ZMod 2) (U.map (Vt S g t).mkQ) = 2 * finrank (ZMod 2)
        ((U ⊓ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t)).map (Vt S g t).mkQ) := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  have hUM : U.map (Vt S g t).mkQ ≤ (Wt S g t).map (Vt S g t).mkQ := Submodule.map_mono hUW
  have : FiniteDimensional (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) := inferInstance
  obtain ⟨h1, h2, h3⟩ := dvd_and_two_mul_of_invariant ρ D.hm D.hdim (aV_ne_zero H ht) D.hQa
    D.Q_bV D.polar_aV_bV hD (fun e => map_mkQ_invariant D hρ hUW hU e)
  have e1 : finrank (ZMod 2) ↥((U.map (Vt S g t).mkQ).comap
      ((Wt S g t).map (Vt S g t).mkQ).subtype) = finrank (ZMod 2) (U.map (Vt S g t).mkQ) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hUM)
  have hT : ((radFix D.Q ⊥ (aV ht) : Subgroup _) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    rw [radFix_bot, ← D.hE]
  have h3' := h3.trans (congrArg (fun T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t) =>
    2 * finrank (ZMod 2) ↥((U.map (Vt S g t).mkQ).comap
      ((Wt S g t).map (Vt S g t).mkQ).subtype ⊓ fixOf ρ T)) hT)
  refine ⟨by rw [← e1]; exact h1, fun hmin => by rw [← e1]; exact h2 fun T _ hT => hmin T hT,
    ?_⟩
  rw [← e1]
  exact h3'.trans (congrArg (fun k => 2 * k) (finrank_inf_fixOf_LmodN D hρ hNo hVU hUW))

theorem comm_sup_Vt_invariant (D : Std H C ht ht1 hVQ) {σ : S.O} (hσM : σ ∈ S.Mbar)
    (hσt : σ * t = t * σ) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∀ r ∈ Rbar S g t, ∀ u ∈ (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔
      Vt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈
        (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t := by
  intro r hr u hu
  obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨w, hw, rfl⟩ := hy
  have hn := comm_mem_Nbar_of_fix H hσM hσt hσV hr
  obtain ⟨n, hndef⟩ : ∃ n, n = r * σ * r⁻¹ * σ⁻¹ := ⟨_, rfl⟩
  rw [← hndef] at hn
  have hrσ : r * σ = n * σ * r := by rw [hndef]; group
  have hw' : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t := apply_mem_Wt H hr hw
  have hσw' : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ hσt hw'
  have h1 := D.hN n hn _ hσw'
  have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) w) =
      ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
        (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) +
      (((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
    rw [← coe_mul_apply r σ w, hrσ, coe_mul_apply, coe_mul_apply]
    abel
  rw [map_add, e]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_right h1)
    (Submodule.mem_sup_left ⟨_, hw', rfl⟩))
    (Submodule.mem_sup_right (apply_mem_Vt_of_mem_Rbar H.conj_mem hr hv))

theorem bad_or_good_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) {x σ : S.O} (hxM : x ∈ S.Mbar) (hxσ : σ = x * t * x⁻¹)
    (hσt : σ * t = t * σ) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    (∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ∨
      (Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∧
        (Wt S g t).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t =
          Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hσM : σ ∈ S.Mbar := by
    rw [hxσ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  set f := (σ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
  set U := (Wt S g t).map f ⊔ Vt S g t with hU
  have hVW := Vt_le_Wt H ht1
  have hUW : U ≤ Wt S g t := by
    refine sup_le ?_ hVW
    rintro _ ⟨w, hw, rfl⟩
    exact (Wt S g t).sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ hσt hw) hw
  have hVU : Vt S g t ≤ U := le_sup_right
  have hUinv := comm_sup_Vt_invariant D hσM hσt hσV
  obtain ⟨-, hdvd, -⟩ := finrank_map_mkQ_of_invariant hCE hNo hΩ D hVU hUW hUinv
  have hdvd4 := hdvd hmin
  rw [hm2] at hdvd4
  have hUle : U ≤ Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    refine sup_le ?_ le_sup_left
    rintro _ ⟨w, -, rfl⟩
    exact Submodule.mem_sup_right (sub_mem_commSpace _ w)
  have hdimσ : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxσ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hdimV := D.hdim
  rw [hm2] at hdimV
  have e1 := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ U
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVU] at e1
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have e3 := Submodule.finrank_mono hUle
  obtain ⟨c, hc⟩ := hdvd4
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  ·
    left
    intro w hw
    have hUV : U = Vt S g t := by
      refine (Submodule.eq_of_le_of_finrank_le hVU ?_).symm
      rw [h0, mul_zero] at hc
      omega
    have hmem : f w ∈ U := Submodule.mem_sup_left ⟨w, hw, rfl⟩
    rw [hUV] at hmem
    exact hmem
  · right
    have hk : finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 0 := by
      have : 4 ≤ finrank (ZMod 2) ↥(U.map (Vt S g t).mkQ) := by
        rw [hc]; norm_num; omega
      omega
    refine ⟨Submodule.finrank_eq_zero.mp hk, ?_⟩
    refine Submodule.eq_of_le_of_finrank_le hUle ?_
    have : 4 ≤ finrank (ZMod 2) ↥(U.map (Vt S g t).mkQ) := by
      rw [hc]; norm_num; omega
    omega

end CFSG.LargeExtraspecial.S8
