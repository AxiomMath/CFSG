module

public import CFSG.LargeExtraspecial.S9RALevi
public import CFSG.LargeExtraspecial.S9GenE
public import CFSG.LargeExtraspecial.S9OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_normalizer_Fbar {t n : S.O} (hnM : n ∈ S.Mbar)
    (hnN : n ∈ normalizer (S.Lbar g : Set S.O)) : n ∈ normalizer (Fbar S g t : Set S.O) := by
  rw [mem_normalizer_iff]
  intro f
  constructor
  · exact conj_mem_Fbar hnM hnN
  · intro hf
    have := conj_mem_Fbar (t := t) (inv_mem hnM) (inv_mem hnN) hf
    simpa [mul_assoc] using this

section Step

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

theorem not_seven_dvd_card_Rbar (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    ¬ 7 ∣ Nat.card (Rbar S g t) := by
  have haQ := H.conj_mem
  have hP := isPGroup_Nbar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hPk : IsPGroup 2 (resV haQ t).ker := fun x => by
    obtain ⟨k, hk⟩ := hP ⟨_, (resV_eq_one_iff haQ x.1).mp x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨a, ha⟩ := hPk.exists_card_eq
  have hrange : Nat.card (resV haQ t).range = 720 := by
    have e1 : (resV haQ t).range = (TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) := by
      rw [range_resV, hSp.eq_sp]
    obtain ⟨e⟩ := S45Q.nonempty_isometryGroup_equiv_perm (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) h4
    rw [e1, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hcard := Subgroup.card_mul_index (resV haQ t).ker
  rw [Subgroup.index_ker, hrange, ha] at hcard
  rw [← hcard]
  intro h7
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h) (by norm_num)
  · exact absurd h (by norm_num)

omit hCE hNo in
theorem exists_Rbar_normalizer_of_fix {e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)}
    (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (aV ht) = aV ht) :
    ∃ r : Rbar S g t, (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t r ∧
      (r : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
  have haQ := H.conj_mem
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hSp.eq_sp]
    exact e.2
  rw [← range_resV haQ t] at heR
  obtain ⟨r, hr⟩ := heR
  refine ⟨r, hr.symm, ?_⟩
  have hfix : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹))
      = S.cl ((1 : S.M) * g * S.z * ((1 : S.M) * g)⁻¹) := by
    have h1 := congrArg Subtype.val (congrArg (fun φ => φ (aV ht)) hr)
    simp only [coe_resV_apply, he] at h1
    simpa [aV] using h1
  have := mem_normalizer_of_fix haQ H.conj_ne (h := 1) (Rbar_le_Mbar r.2) hfix
  simpa using this

theorem nqSub_Fbar_le_fixOf [hN : NQHyp S g t] {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    nqSub S g t (Fbar S g t) ≤ S2.fixOf (nqRep S g t hSp.eq_sp)
      (spPointRadical (beta H C ht ht1 hVQ) (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have h1 := pair_one (t := t) hb
  have hT : (spPointRadical (beta H C ht ht1 hVQ) (aV ht) :
      Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t 1 := by
    rw [← hSp.LmodN_eq]
    ext e
    simp only [SetLike.mem_coe, LmodN, LhmodN, OneMemClass.coe_one, one_mul]
  rw [fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hSp.eq_sp h1.1 hT]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, by simpa using (Fbar_le_Lbar : Fbar S g t ≤ S.Lbar g) hx, rfl⟩

omit hCE hNo in
theorem nqRep_mem_nqSub_Fbar [hN : NQHyp S g t]
    {e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)}
    (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (aV ht) = aV ht) {u : NQ S g t}
    (hu : u ∈ nqSub S g t (Fbar S g t)) :
    nqRep S g t hSp.eq_sp e u ∈ nqSub S g t (Fbar S g t) := by
  have hr' := exists_Rbar_normalizer_of_fix H C ht ht1 hVQ hSp (e := e) he
  obtain ⟨r, her, hrN⟩ := hr'
  obtain ⟨f, hf, hfu⟩ := hu
  subst hfu
  simp only [nqRep_apply hSp.eq_sp her]
  exact ⟨_, conj_mem_Fbar (Rbar_le_Mbar r.2) hrN hf, rfl⟩

theorem finrank_nqSub_Fbar [hN : NQHyp S g t] {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) :
    finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 0 ∨
      finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 2 := by
  have haQ := H.conj_mem
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  have hFN : conjL S g t ⊆ Nbar S g t := by
    rintro τ ⟨hτL, x, hxM, rfl⟩
    exact hL x hxM hτL
  have hkey : ∀ τ ∈ conjL S g t, τ ≠ t → ∃ y ∈ Nbar S g t, y * τ * y⁻¹ = τ * t := by
    rintro τ ⟨hτL, x, hxM, rfl⟩ hne
    exact exists_conj_eq_mul_t hCE H hNo C ht ht1 hVQ hSp hxM ⟨hτL, hL x hxM hτL⟩ hne
  have hFL : Fbar S g t ≤ S.Lbar g := Fbar_le_Lbar
  have hUfix : nqSub S g t (Fbar S g t) ≤ S2.fixOf (nqRep S g t hSp.eq_sp)
      (spPointRadical (beta H C ht ht1 hVQ) (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) := by
    have h1 := pair_one (t := t) hb
    have hT : (spPointRadical (beta H C ht ht1 hVQ) (aV ht) :
        Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t 1 := by
      rw [← hSp.LmodN_eq]
      ext e
      simp only [SetLike.mem_coe, LmodN, LhmodN, OneMemClass.coe_one, one_mul]
    rw [fixOf_nqRep_eq H hNo C ht ht1 hVQ hgen hN0 hh hb hSp.eq_sp h1.1 hT]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hFL hx, rfl⟩
  obtain ⟨ex, ey, hex, hey, hexx, heyy, hlevi⟩ := exists_levi_pair (nqRep S g t hSp.eq_sp)
    (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) h4
    (beta_aV_bV H C ht ht1 hVQ hh hb) hD
  have hrx' := exists_Rbar_normalizer_of_fix H C ht ht1 hVQ hSp (e := ex) hex
  have hry' := exists_Rbar_normalizer_of_fix H C ht ht1 hVQ hSp (e := ey) hey
  obtain ⟨rx, hrx, hrxN⟩ := hrx'
  obtain ⟨ry, hry, hryN⟩ := hry'
  have hinvF : ∀ (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (r : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t r →
      (r : S.O) ∈ normalizer (S.Lbar g : Set S.O) → ∀ u ∈ nqSub S g t (Fbar S g t),
        nqRep S g t hSp.eq_sp e u ∈ nqSub S g t (Fbar S g t) := by
    rintro e r her hrN u ⟨f, hf, hfu⟩
    subst hfu
    simp only [nqRep_apply hSp.eq_sp her]
    exact ⟨_, conj_mem_Fbar (Rbar_le_Mbar r.2) hrN hf, rfl⟩
  have hzero : (∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp ex u = u) →
      (∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp ey u = u) →
      finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 0 := by
    intro hx hy
    rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro u hu
    exact hlevi u (hUfix hu) (hx u hu) (hy u hu)
  by_contra hcon
  push Not at hcon
  have hfixall : ∀ (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (r' : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t r' →
      (r' : S.O) ∈ normalizer (S.Lbar g : Set S.O) →
      ∀ u ∈ nqSub S g t (Fbar S g t), nqRep S g t hSp.eq_sp e u = u := by
    intro e r' her hrN
    have hcase := Nat.lt_or_ge (finrank (ZMod 2) (nqSub S g t (Fbar S g t))) 3
    rcases hcase with hlt | hge
    ·
      have hr1 : finrank (ZMod 2) (nqSub S g t (Fbar S g t)) = 1 := by omega
      intro u hu
      by_cases hu0 : u = 0
      · rw [hu0, map_zero]
      have hv := hinvF e r' her hrN u hu
      have hne : nqRep S g t hSp.eq_sp e u ≠ 0 := fun h0 =>
        hu0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
      exact eq_of_finrank_le_one (by rw [hr1]) hv hu hne hu0
    · have hcase2 := fix_or_prod_dvd_card H C ht hFN hkey hge
      rcases hcase2 with hall | hdvd
      · rintro u ⟨f, hf, hfu⟩
        subst hfu
        simp only [nqRep_apply hSp.eq_sp her]
        rw [nqMk_eq_iff, coe_nConj]
        exact hall r' ⟨r'.2, mem_normalizer_Fbar (Rbar_le_Mbar r'.2) hrN⟩ f hf
      · exfalso
        apply not_seven_dvd_card_Rbar hCE H hNo C ht ht1 hVQ hSp h4
        refine dvd_trans (dvd_trans ?_ hdvd) (Subgroup.card_dvd_of_le inf_le_left)
        have h3 : 2 ∈ Finset.range (finrank (ZMod 2) (nqSub S g t (Fbar S g t))) :=
          Finset.mem_range.mpr (by omega)
        exact Finset.dvd_prod_of_mem _ h3
  exact hcon.1 (hzero (hfixall ex rx hrx hrxN) (hfixall ey ry hry hryN))


end Step

end CFSG.LargeExtraspecial.S9
