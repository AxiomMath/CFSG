module

public import CFSG.LargeExtraspecial.S9PA
public import CFSG.LargeExtraspecial.S45QMain
public import CFSG.LargeExtraspecial.S5Fac
public import CFSG.LargeExtraspecial.S6TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Hom

variable {R A : Type*} [Group R] [Group A] (φ : R →* A)

theorem commute_of_map_commutator_eq_one {n s : R} (h : φ (n * s * n⁻¹ * s⁻¹) = 1) :
    Commute (φ n) (φ s) := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
  calc φ n * φ s = (φ n * φ s * (φ n)⁻¹ * (φ s)⁻¹) * (φ s * φ n) := by group
    _ = φ s * φ n := by rw [h, one_mul]

theorem map_conj_eq_of_commute {a b : R} (h : Commute (φ a) (φ b)) : φ (a * b * a⁻¹) = φ b := by
  rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right]

end Hom

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def rhoWV (H : Hyp4 S g) (t : S.O) :
    Rbar S g t →* (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)) :=
  secHom S g t (Vt S g t) (Wt S g t)
    (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
    (fun _ hx _ hv => apply_mem_Wt H hx hv)

theorem rhoWV_eq_one_iff (H : Hyp4 S g) {t : S.O} (r : Rbar S g t) :
    rhoWV S g H t r = 1 ↔ ∀ w ∈ Wt S g t, ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  constructor
  · intro h1 w hw
    refine (secHom_fix_iff (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
      (fun _ hx _ hv => apply_mem_Wt H hx hv) r hw).mp ?_
    change rhoWV S g H t r (secMk (Vt S g t) hw) = secMk (Vt S g t) hw
    rw [h1]
    rfl
  · intro h
    refine LinearEquiv.ext fun m => ?_
    obtain ⟨w, hw, rfl⟩ := exists_secMk (Vt S g t) m
    exact (secHom_fix_iff (fun _ hx _ hv => apply_mem_Vt_of_mem_Rbar H.conj_mem hx hv)
      (fun _ hx _ hv => apply_mem_Wt H hx hv) r hw).mpr (h w hw)

theorem apply_sub_mem_Vt_of_rhoWV_eq (H : Hyp4 S g) {t : S.O} {r s : Rbar S g t}
    (hrs : rhoWV S g H t r = rhoWV S g H t s) {w : S.Qt} (hw : w ∈ Wt S g t) :
    ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - ((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Vt S g t := by
  have h1 : ((rhoWV S g H t r (secMk (Vt S g t) hw) : _) : S.Qt ⧸ Vt S g t) =
      (Vt S g t).mkQ (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := rfl
  have h2 : ((rhoWV S g H t s (secMk (Vt S g t) hw) : _) : S.Qt ⧸ Vt S g t) =
      (Vt S g t).mkQ (((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := rfl
  rw [hrs] at h1
  exact (Submodule.Quotient.eq _).mp (h1.symm.trans h2)

section P1

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hP : PGL25Case H C ht ht1 hVQ)
include H C ht ht1 hVQ hP

theorem forall_comm_rhoWV_pgl25 {τ : S.O} (hτL : τ ∈ S.Lbar g) (hτN : τ ∉ Nbar S g t)
    (hfix : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    ∀ r s : Rbar S g t, Commute (rhoWV S g H t r) (rhoWV S g H t s) := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hP.tau_not_mem
  have hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  have hD := dtEqConj_of_pgl25Case H C hP
  have hN0W : ∀ x ∈ N0bar S g t, ∀ w ∈ Wt S g t,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t :=
    fun x hx w hw => apply_sub_mem_Vt_of_mem_N0bar H
      (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hPab hk hw) hx hw
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have h15 : 15 ∣ Nat.card (RmodN S g t) :=
    S45Q.fifteen_dvd_card_of_transitive hP.finrank_eq (aV_ne_zero H ht) hP.transitive
  obtain ⟨M₀, hM₀X, hM₀n, hM₀s, hM₀i⟩ := S45Q.exists_simple_normal_of_fifteen_dvd
    (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) hP.finrank_eq
    (RmodN_le_isometryGroup H C ht ht1 hVQ) h15
  have hrange : ∀ x : Rbar S g t, resV haQ t x ∈ RmodN S g t := fun x => by
    rw [← range_resV haQ t]; exact ⟨x, rfl⟩
  refine forall_comm_of_exists_trivial (resV haQ t) (rhoWV S g H t) (M₀ := M₀) ?_ ?_ hM₀s ?_ ?_
    (τ := ⟨τ, Lbar_le_Rbar ht hτL⟩) ((rhoWV_eq_one_iff H _).mpr hfix)
    (fun h1 => hτN ((resV_eq_one_iff haQ _).mp h1)) ?_
  · intro m hm
    have hmR := hM₀X hm
    rw [← range_resV haQ t] at hmR
    exact hmR
  · intro x m hm
    have := hM₀n.conj_mem ⟨m, hM₀X hm⟩ (mem_subgroupOf.mpr hm) ⟨resV haQ t x, hrange x⟩
    rw [mem_subgroupOf] at this
    simpa using this
  · intro x y hx hy
    have hx' : (⟨resV haQ t x, hrange x⟩ : RmodN S g t) ∉ M₀.subgroupOf (RmodN S g t) :=
      fun h => hx (mem_subgroupOf.mp h)
    have hy' : (⟨resV haQ t y, hrange y⟩ : RmodN S g t) ∉ M₀.subgroupOf (RmodN S g t) :=
      fun h => hy (mem_subgroupOf.mp h)
    have hI : (M₀.subgroupOf (RmodN S g t)).index = 2 := by
      have h0 : (M₀.subgroupOf (RmodN S g t)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1 : (M₀.subgroupOf (RmodN S g t)).index ≠ 1 := fun h1 =>
        hx' (by rw [Subgroup.index_eq_one.mp h1]; exact mem_top _)
      have h2 : (M₀.subgroupOf (RmodN S g t)).index ≤ 2 := hM₀i
      omega
    have hiff : (⟨resV haQ t x, hrange x⟩ : RmodN S g t)⁻¹ ∈ M₀.subgroupOf (RmodN S g t) ↔
        (⟨resV haQ t y, hrange y⟩ : RmodN S g t) ∈ M₀.subgroupOf (RmodN S g t) :=
      ⟨fun h => absurd (by simpa using inv_mem h) hx', fun h => absurd h hy'⟩
    have hmem := (Subgroup.mul_mem_iff_of_index_two hI).mpr hiff
    rw [mem_subgroupOf] at hmem
    rw [map_mul, map_inv]
    simpa using hmem
  · intro n hn s
    have hnN : (n : S.O) ∈ Nbar S g t := (resV_eq_one_iff haQ n).mp hn
    refine commute_of_map_commutator_eq_one _ ((rhoWV_eq_one_iff H _).mpr fun w hw => ?_)
    exact hN0W _ (by simpa using commutator_mem_N0bar H hD hnN s.2) w hw
  · intro hcen
    have hea : resV haQ t ⟨τ, Lbar_le_Rbar ht hτL⟩ (aV ht) = aV ht :=
      (mem_spPointRadical.mp (LmodN_le_spPointRadical H C ht ht1 hVQ
        (S5.resV_mem_LmodN haQ hτL (Lbar_le_Rbar ht hτL)))).2.1
    have hfixv : ∀ v : Vt S g t, resV haQ t ⟨τ, Lbar_le_Rbar ht hτL⟩ v = v := by
      intro v
      by_cases hv0 : v = 0
      · rw [hv0, map_zero]
      obtain ⟨x, hx, hxa⟩ := hP.transitive v hv0
      rw [← range_resV haQ t] at hx
      obtain ⟨r, rfl⟩ := hx
      have h1 := LinearEquiv.congr_fun (hcen r) (aV ht)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hea] at h1
      rw [← hxa]
      exact h1.symm
    exact LinearEquiv.ext hfixv

theorem false_of_fix_WV_pgl25 (hNo : NoA2 S g) (hn : 4 < S.width) {τ : S.O}
    (hτL : τ ∈ S.Lbar g) (hτN : τ ∉ Nbar S g t)
    (hfix : ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) : False := by
  have hcomm := forall_comm_rhoWV_pgl25 H C ht ht1 hVQ hP hτL hτN hfix
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ hP.tau_not_mem
  have hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR
  have hPI := pairInt_of_radBound H C ht ht1 hVQ hR
  have hD := dtEqConj_of_pgl25Case H C hP
  obtain ⟨k, hk, hLk⟩ := hD h (mem_Lbar_of_pair H ht hh)
  have hsame : ∀ l ∈ S.Lbar g, ∀ w ∈ Wt S g t,
      ((S.ρ k * l * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w -
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Vt S g t := by
    intro l hl w hw
    exact apply_sub_mem_Vt_of_rhoWV_eq H (map_conj_eq_of_commute _ (hcomm ⟨S.ρ k, hk⟩
      ⟨l, Lbar_le_Rbar ht hl⟩)) hw
  have hLb : ∀ l' ∈ S.Lbar ((h : G) * g), ∃ l ∈ S.Lbar g, S.ρ k * l * (S.ρ k)⁻¹ = l' := by
    intro l' hl'
    rw [hLk, Lbar_mul S k g] at hl'
    obtain ⟨l, hl, rfl⟩ := hl'
    exact ⟨l, hl, rfl⟩
  have hLb' : ∀ l ∈ S.Lbar g, S.ρ k * l * (S.ρ k)⁻¹ ∈ S.Lbar ((h : G) * g) := by
    intro l hl
    rw [hLk, Lbar_mul S k g]
    exact ⟨l, hl, rfl⟩
  have hint := sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb hPab
  have hA : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ≤ Vt S g t := by
    intro w hw
    have hwW : w ∈ Wt S g t := hw.2
    have hwa := (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hwW).mpr
      (Submodule.mem_sup_left hw)
    have hwb : ∀ l' ∈ S.Lbar ((h : G) * g),
        (l' : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
      intro l' hl'
      obtain ⟨l, hl, rfl⟩ := hLb l' hl'
      have e : ((S.ρ k * l * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
          (((S.ρ k * l * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w -
            (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
      rw [e]
      exact add_mem (hsame l hl w hwW) (hwa l hl)
    have hmem : w ∈ ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊓
        ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) :=
      ⟨Submodule.mem_sup_left hw,
        (forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hwW).mp hwb⟩
    rwa [hint] at hmem
  have hB : S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t ≤ Vt S g t := by
    intro w hw
    have hwW : w ∈ Wt S g t := hw.2
    have hwb := (forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hwW).mpr
      (Submodule.mem_sup_left hw)
    have hwa : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
      intro l hl
      have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
          -(((S.ρ k * l * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w -
            (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
          (((S.ρ k * l * (S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
      rw [e]
      exact add_mem (neg_mem (hsame l hl w hwW)) (hwb _ (hLb' l hl))
    have hmem : w ∈ ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊓
        ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) :=
      ⟨(forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hwW).mp hwa,
        Submodule.mem_sup_left hw⟩
    rwa [hint] at hmem
  have hWV : Wt S g t ≤ Vt S g t := by
    rw [← sup_eq_Wt H C ht ht1 hVQ hh hb hPab]
    exact sup_le hA hB
  have h1 := Submodule.finrank_mono hWV
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have h3 := S.finrank_Qt_eq_two_mul_width
  rw [hP.finrank_eq] at h1 h2
  omega

end P1

end CFSG.LargeExtraspecial.S9
