module

public import CFSG.LargeExtraspecial.S6Four
public import CFSG.LargeExtraspecial.S5Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_zpowers_eq_two (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    Nat.card (zpowers t) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_mem_Lbar S H.conj_mem ht) ht1

theorem mem_zpowers_iff_of_mem_Lbar (H : Hyp4 S g) {t x : S.O} (ht : t ∈ S.Lbar g) :
    x ∈ zpowers t ↔ x = 1 ∨ x = t :=
  Setting.mem_zpowers_iff_of_mul_self (mul_self_of_mem_Lbar S H.conj_mem ht)

theorem Lbar_inf_Nbar_eq {t : S.O} (ht : t ∈ S.Lbar g) (hN : Nbar S g t = zpowers t) :
    S.Lbar g ⊓ Nbar S g t = zpowers t := by
  rw [hN]
  exact inf_eq_right.mpr (zpowers_le.mpr ht)

theorem two_pow_width_sub_one (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hN : Nbar S g t = zpowers t) :
    2 ^ (S.width - 1) = 2 * Nat.card (LmodN S g t) := by
  have h1 := card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, Lbar_inf_Nbar_eq ht hN, card_zpowers_eq_two H ht ht1] at h1
  rw [h1, mul_comm]

theorem eq_of_two_pow_eq {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b :=
  Nat.pow_right_injective le_rfl h

section Cases

variable (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  (ht1 : t ≠ 1) (hN : Nbar S g t = zpowers t)
include H C ht ht1 hN

theorem width_eq_of_linCase (hL : LinCase S g ht) :
    S.width = finrank (ZMod 2) (Vt S g t) + 1 := by
  have h1 := two_pow_width_sub_one H C ht ht1 hN
  rw [hL.LmodN_eq, card_centreGroup (aV_ne_zero H ht), ← pow_succ'] at h1
  have h2 := eq_of_two_pow_eq h1
  have h3 := hL.two_le_finrank
  have h4 := H.two_lt_width
  omega

omit hN in
theorem card_LmodN_of_omegaCase {hVQ : ¬ V S g t ≤ S.Qa g} (hΩ : OmegaCase H C ht ht1 hVQ) :
    Nat.card (LmodN S g t) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 2) := by
  obtain ⟨Q, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
  have hQa : Q (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
  rw [hE, card_pointRadical hQ (aV_ne_zero H ht) hQa]

include hNo in
theorem width_eq_finrank_of_omegaCase {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) : S.width = finrank (ZMod 2) (Vt S g t) := by
  have h1 := two_pow_width_sub_one H C ht ht1 hN
  rw [card_LmodN_of_omegaCase H C ht ht1 hΩ, ← pow_succ'] at h1
  have h2 := eq_of_two_pow_eq h1
  have h3 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have h4 := H.two_lt_width
  omega

theorem width_eq_four_of_tau_not_mem {hVQ : ¬ V S g t ≤ S.Qa g}
    (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t) :
    S.width = 4 := by
  have h1 := two_pow_width_sub_one H C ht ht1 hN
  have h2 := S5.card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ h4 hτ
  have h3 := finrank_Vt_le_width H ht1
  have h5 : 2 ^ (S.width - 1) ≤ 2 ^ 3 := by rw [h1]; omega
  have h6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h5
  omega

theorem timmesfeld_7_5 {hVQ : ¬ V S g t ≤ S.Qa g} (hA : A6Case H C ht ht1 hVQ) :
    S.width = 4 :=
  width_eq_four_of_tau_not_mem H C ht ht1 hN hA.finrank_eq hA.tau_not_mem

theorem width_eq_four_of_pgl25Case {hVQ : ¬ V S g t ≤ S.Qa g}
    (hP : PGL25Case H C ht ht1 hVQ) : S.width = 4 :=
  width_eq_four_of_tau_not_mem H C ht ht1 hN hP.finrank_eq hP.tau_not_mem

include hNo in
theorem not_spCase (hCE : CentralExtInput.{u}) {hVQ : ¬ V S g t ≤ S.Qa g} :
    ¬ SpCase H C ht ht1 hVQ := by
  intro hSp
  have h := timmesfeld_6_4 hCE H hNo C ht ht1 hVQ hSp
  rw [Lbar_inf_Nbar_eq ht hN] at h
  exact lt_irrefl _ h

end Cases

end CFSG.LargeExtraspecial.S7
