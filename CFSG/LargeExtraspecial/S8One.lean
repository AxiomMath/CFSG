module

public import CFSG.LargeExtraspecial.S8Ten
public import CFSG.LargeExtraspecial.S8Flag
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

theorem four_mul_lt_two_pow {m : ℕ} (hm : 6 ≤ m) : 4 * m < 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
      ring
    rw [e]
    omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem finrank_commWV_add_one_le_of_transvection (D : Std H C ht ht1 hVQ) {x τ : S.O}
    (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ) {d : Vt S g t} (hd : D.Q d = 1)
    (hτd : ∀ v : Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt)) :
    finrank (ZMod 2) (commWV S g t τ) + 1 ≤ finrank (ZMod 2) (Vt S g t) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨y, hy⟩ : ∃ y : Vt S g t, polar D.Q y d = 1 := by
    obtain ⟨y, hy⟩ := (exists_mem_perp_polar_eq_one D.hQ (F := ⊥) (bot_inf_eq _)
      (by rw [perp_bot]; exact Submodule.mem_top) hd0)
    exact ⟨y, hy.2⟩
  refine finrank_commWV_add_one_le H C ht ht1 hVQ hxτ hτt y.2 ?_
  rw [hτd y, hy, one_smul]
  intro h
  apply hd0
  have : (d : S.Qt) = 0 := by
    have h' := congrArg (· - (y : S.Qt)) h
    simpa using h'
  exact Subtype.ext this

theorem not_transvection (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (hcase : 4 * D.m < 2 ^ (D.m - 1) + 2 ∨ (D.IsMinus ∧ 4 * D.m < 2 ^ D.m + 2) ∨
      (D.m = 5 ∧ ¬ D.IsMinus) ∨ (D.IsMinus ∧ D.m = 3 ∧ S.width ≠ 10))
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    {d : Vt S g t} (hd : D.Q d = 1)
    (hτd : ∀ v : Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt)) :
    False := by
  have hlow := finrank_WV_le_two_mul_finrank_commWV D hfus hxM hxτ hτt hd hτd
  have hup := finrank_commWV_add_one_le_of_transvection D hxτ hτt hd hτd
  rw [D.hdim] at hup
  have hpos := D.pos_finrank_WV hA7
  have hm := D.hm
  have hdvd := timmesfeld_6_1_two_dvd hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE D.hQa
    D.polar_aV_bV (m := D.m) (by omega) D.hdim
  rcases hcase with h | ⟨hmin, h⟩ | ⟨h5, hplus⟩ | ⟨hmin, h3, hw⟩
  · have := Nat.le_of_dvd hpos hdvd
    omega
  · have hdvd' := timmesfeld_6_1_two_dvd_minus hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
      D.hQa D.polar_aV_bV hm D.hdim hmin
    have := Nat.le_of_dvd hpos hdvd'
    omega
  · exact false_of_transvection_ten hCE hNo hΩ D hfus hA7 h5 hplus hxM hxτ hτt hd hτd
  · have hdvd' := timmesfeld_6_1_two_dvd_minus hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
      D.hQa D.polar_aV_bV hm D.hdim hmin
    rw [h3] at hdvd' hup
    obtain ⟨c, hc⟩ := hdvd'
    have hw' := D.finrank_WV
    rw [h3] at hw'
    norm_num at hc
    omega

theorem flag_of_sub (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (hcase : 4 * D.m < 2 ^ (D.m - 1) + 2 ∨ (D.IsMinus ∧ 4 * D.m < 2 ^ D.m + 2) ∨
      (D.m = 5 ∧ ¬ D.IsMinus) ∨ (D.IsMinus ∧ D.m = 3 ∧ S.width ≠ 10))
    (hbig : 2 * D.m < 2 ^ (D.m - 1) ∨ (D.IsMinus ∧ 2 * D.m < 2 ^ D.m)) :
    ∀ τ ∈ conjCentM S t, (∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  rintro τ ⟨-, hτt, x, hxM, hxτ⟩
  by_cases hτN : τ ∈ Nbar S g t
  · exact ⟨(mem_Nbar.mp hτN).2, D.hN τ hτN⟩
  rcases eq_one_or_transvection D hfus hsub hxM hxτ hτt hτN with hV | ⟨d, hd, hτd⟩
  · exact ⟨hV, fix_Wt_of_fix_Vt hCE hNo hΩ D hxM hxτ hτt hV hbig⟩
  · exact (not_transvection hCE hNo hΩ D hfus hA7 hcase hxM hxτ hτt hd hτd).elim

theorem timmesfeld_8_1 (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (h44 : ¬ (D.m = 2 ∧ ¬ D.IsMinus)) :
    (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
      (D.m = 2 ∧ D.IsMinus) ∨ D.m = 3 ∨ (D.m = 4 ∧ ¬ D.IsMinus) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hsub, h2, h3, h4⟩ := hcon
  have hm := D.hm
  have hm4 : 4 ≤ D.m := by
    by_contra hlt
    have hm2 : D.m = 2 := by omega
    exact h44 ⟨hm2, h2 hm2⟩
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  obtain ⟨hsimp, hnab⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6
  have hn : 4 < S.width := by have := D.finrank_WV; omega
  have hcase : 4 * D.m < 2 ^ (D.m - 1) + 2 ∨ (D.IsMinus ∧ 4 * D.m < 2 ^ D.m + 2) ∨
      (D.m = 5 ∧ ¬ D.IsMinus) ∨ (D.IsMinus ∧ D.m = 3 ∧ S.width ≠ 10) := by
    rcases Nat.lt_or_ge D.m 6 with h | h
    · rcases Nat.lt_or_ge D.m 5 with h' | h'
      · have hm4' : D.m = 4 := by omega
        right; left
        exact ⟨h4 hm4', by rw [hm4']; norm_num⟩
      · have hm5 : D.m = 5 := by omega
        by_cases hmin : D.IsMinus
        · right; left; exact ⟨hmin, by rw [hm5]; norm_num⟩
        · right; right; left; exact ⟨hm5, hmin⟩
    · left
      have := four_mul_lt_two_pow h
      omega
  have hbig : 2 * D.m < 2 ^ (D.m - 1) ∨ (D.IsMinus ∧ 2 * D.m < 2 ^ D.m) := by
    rcases Nat.lt_or_ge D.m 5 with h' | h'
    · have hm4' : D.m = 4 := by omega
      right
      exact ⟨h4 hm4', by rw [hm4']; norm_num⟩
    · left
      rcases Nat.lt_or_ge D.m 6 with h | h
      · have hm5 : D.m = 5 := by omega
        rw [hm5]; norm_num
      · have := four_mul_lt_two_pow h
        omega
  exact hA7 (Abar_eq_of_flag hCorB hFacts hCE hIrr hNo hn D hfus le_rfl hsimp hnab
    (flag_of_sub hCE hNo hΩ D hfus hsub hA7 hcase hbig))

theorem timmesfeld_8_2 (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (hm3 : D.m = 3) (hmin : D.IsMinus) :
    (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨ S.width = 10 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hsub, hw⟩ := hcon
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim, hm3]
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  obtain ⟨hsimp, hnab⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6
  have hn : 4 < S.width := by have := D.finrank_WV; omega
  exact hA7 (Abar_eq_of_flag hCorB hFacts hCE hIrr hNo hn D hfus le_rfl hsimp hnab
    (flag_of_sub hCE hNo hΩ D hfus hsub hA7 (Or.inr (Or.inr (Or.inr ⟨hmin, hm3, hw⟩)))
      (Or.inr ⟨hmin, by rw [hm3]; norm_num⟩)))

end CFSG.LargeExtraspecial.S8
