module

public import CFSG.LargeExtraspecial.S9Four
public import CFSG.LargeExtraspecial.S6ThreeH
public import CFSG.LargeExtraspecial.S8FusB
public import CFSG.LargeExtraspecial.S9ModB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem four_mul_lt_four_add_two_pow {m : ℕ} (hm : 4 ≤ m) : 4 * m < 4 + 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem eight_mul_lt_sixteen_add_two_pow {m : ℕ} (hm : 5 ≤ m) : 8 * m < 16 + 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem arith_9_4 {m k n D a b c : ℕ} (hk : k = m + m) (h4 : 4 ≤ k) (hflag : 2 * a + b ≤ k)
    (hw1 : D + 2 * (k + 1) = 2 * n) (hn : k + 2 ≤ n) (hc : D = 2 ^ m * c)
    (hcase : (a = 2 ∧ D ≤ 4 * b) ∨ (1 ≤ a ∧ 2 * b = D)) :
    (k = 4 ∧ n = 7) ∨ (k = 6 ∧ n = 11) ∨ (k = 8 ∧ n = 17) := by
  have hm2 : 2 ≤ m := by omega
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc
      omega
    · exact h0
  have hpow : 2 ^ m ≤ D := hc ▸ Nat.le_mul_of_pos_right _ hc1
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · interval_cases m <;> norm_num at hc <;> omega
    · have := eight_mul_lt_sixteen_add_two_pow hm5
      omega
  · rcases Nat.lt_or_ge m 4 with hm4 | hm4
    · interval_cases m <;> norm_num at hc <;> omega
    · have := four_mul_lt_four_add_two_pow hm4
      omega

theorem finrank_add_two_le_width (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : finrank (ZMod 2) (Vt S g t) + 2 ≤ S.width := by
  have hcard := card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := by
    rw [zpowers_le]
    exact ⟨ht, self_mem_Nbar H ht⟩
  have hlt : Nat.card (zpowers t) < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hA))
  rw [Nat.card_zpowers, hto, hcard] at hlt
  have : 1 < S.width - finrank (ZMod 2) (Vt S g t) := by
    by_contra hc
    push Not at hc
    have : 2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) hc
    omega
  omega

theorem timmesfeld_9_4_count (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O}
    (hxL : x * t * x⁻¹ ∈ S.Lbar g) (hxN : x * t * x⁻¹ ∉ Nbar S g t) :
    (finrank (ZMod 2) (Vt S g t) = 4 ∧ S.width = 7) ∨
      (finrank (ZMod 2) (Vt S g t) = 6 ∧ S.width = 11) ∨
        (finrank (ZMod 2) (Vt S g t) = 8 ∧ S.width = 17) := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_3_three hCE H hNo C ht ht1 hVQ hSp hh hb
  have hτR : x * t * x⁻¹ ∈ Rbar S g t := Lbar_le_Rbar ht hxL
  obtain ⟨r, hr⟩ : ∃ r : Rbar S g t, (r : S.O) = x * t * x⁻¹ := ⟨⟨_, hτR⟩, rfl⟩
  have heI : resV haQ t r ∈ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := by
    rw [← hSp.eq_sp, ← range_resV haQ t]
    exact ⟨r, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV haQ t r := ⟨⟨_, heI⟩, rfl⟩
  have heU : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
      spPointRadical (beta H C ht ht1 hVQ) (aV ht) := by
    rw [← hSp.LmodN_eq, he]
    exact ⟨x * t * x⁻¹, hxL, fun v => by rw [coe_resV_apply, hr]⟩
  have he1 : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1 := by
    intro h1
    rw [he] at h1
    exact hxN (hr ▸ (resV_eq_one_iff haQ r).mp h1)
  have hflag := finrank_commSpace_ge hCE H hNo C ht ht1 hVQ hSp hh hb r.2
  rw [finrank_map_Vt_eq haQ r, ← finrank_commSpace_secMk haQ ρ hρ e r he] at hflag
  have hcomm : finrank (ZMod 2) (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1, LinearEquiv.finrank_map_eq]
  rw [hr, hcomm] at hflag
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have hdvd := timmesfeld_6_3_three_dvd hCE H hNo C ht ht1 hVQ hSp hh hb (m := m) (by omega)
  have hw1 := finrank_w1v1 H C ht ht1 hVQ hh hb
  have hV1 := finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb
  have hn := finrank_add_two_le_width H C ht ht1 hVQ hSp hA
  obtain ⟨c, hc⟩ := hdvd
  have hpp : beta H C ht ht1 hVQ (bV (mem_Lbar_of_pair H ht hh)) (aV ht) = 1 := by
    rw [beta_symm]
    exact beta_aV_bV H C ht ht1 hVQ hh hb
  have hV1le : 1 ≤ finrank (ZMod 2) (commSpace (resV haQ t r)) := by
    rw [← he]
    exact one_le_finrank_commSpace he1
  by_cases ha2 : IsSpTypeA (beta H C ht ht1 hVQ) (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) 2
  · have h1 := le_four_mul_finrank_commSpace ρ (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) (m := m) (by omega) hpp hD.symm e heU he1
    have h2 : finrank (ZMod 2) (commSpace (resV haQ t r)) = 2 := he ▸ ha2.2.2.2.1
    exact arith_9_4 hm h4 hflag (by omega) hn hc (Or.inl ⟨h2, h1⟩)
  · have h1 := two_mul_finrank_commSpace ρ (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) (m := m) (by omega) hpp hD.symm e heU he1 ha2
    exact arith_9_4 hm h4 hflag (by omega) hn hc (Or.inr ⟨hV1le, h1⟩)

end CFSG.LargeExtraspecial.S9
