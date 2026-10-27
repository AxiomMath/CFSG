module

public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S8Dim4
public import CFSG.LargeExtraspecial.S8FiveC
public import CFSG.LargeExtraspecial.S8One

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

theorem params_of_transvection {m n d : ℕ} (hm : m = 3 ∨ m = 4) (hd : 0 < d)
    (hdvd : 2 ^ (m - 1) ∣ d) (h4 : m = 3 → d ≠ 4) (hle : d ≤ 2 * (2 * m - 1))
    (hn : d + 4 * m = 2 * n) : (m = 3 ∧ n = 10) ∨ (m = 4 ∧ n = 12) := by
  obtain ⟨c, rfl⟩ := hdvd
  rcases hm with rfl | rfl
  · left
    norm_num at hle hd h4 hn ⊢
    omega
  · right
    norm_num at hle hd hn ⊢
    omega

theorem step1_fix_Vt (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (hm : D.m = 3 ∨ D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hn : ¬ ((D.m = 3 ∧ S.width = 10) ∨ (D.m = 4 ∧ S.width = 12))) :
    ∀ τ ∈ conjCentM S t, ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  rintro τ ⟨-, hτt, x, hxM, hxτ⟩
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  by_cases hτN : τ ∈ Nbar S g t
  · exact (mem_Nbar.mp hτN).2
  rcases eq_one_or_transvection D hfus hsub hxM hxτ hτt hτN with hV | ⟨d, hd, hτd⟩
  · exact hV
  exfalso
  apply hn
  have hlow := finrank_WV_le_two_mul_finrank_commWV D hfus hxM hxτ hτt hd hτd
  have hup := finrank_commWV_add_one_le_of_transvection D hxτ hτt hd hτd
  rw [D.hdim] at hup
  have hpos := D.pos_finrank_WV hA7
  have hm2 := D.hm
  have hdvd := timmesfeld_6_1_two_dvd hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE D.hQa
    D.polar_aV_bV (m := D.m) (by omega) D.hdim
  have h4 : D.m = 3 → finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≠ 4 :=
    fun h3 => finrank_WV_ne_four hCE hNo hΩ D (Or.inl (by omega))
  exact params_of_transvection hm hpos hdvd h4 (by omega) D.finrank_WV

theorem step2_exists_not_mem_Nbar (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (hm : 3 ≤ D.m) :
    ∃ τ ∈ conjCentM S t, τ ∉ Nbar S g t := by
  by_contra hcon
  push Not at hcon
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  obtain ⟨hsimp, hnab⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6
  have hn : 4 < S.width := by have := D.finrank_WV; omega
  exact hA7 (Abar_eq_of_flag hCorB hFacts hCE hIrr hNo hn D hfus le_rfl hsimp hnab
    fun τ hτ => ⟨(mem_Nbar.mp (hcon τ hτ)).2, D.hN τ (hcon τ hτ)⟩)

theorem exists_Nbar_conj_eq_mul_of_mem_Abar (D : Std H C ht ht1 hVQ) {τ : S.O}
    (hτA : τ ∈ S.Lbar g ⊓ Nbar S g t) (hτt : τ ∉ zpowers t) :
    ∃ n ∈ Nbar S g t, n * τ * n⁻¹ = τ * t := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hnc : ¬ ∀ n ∈ Nbar S g t, n * τ = τ * n := fun h =>
    hτt (A1_le_zpowers D (mem_A1.mpr ⟨hτA.1, hτA.2, h⟩))
  push Not at hnc
  obtain ⟨n, hn, hnτ⟩ := hnc
  refine ⟨n, hn, ?_⟩
  have hc := D.hNc n hn τ hτA.2
  rcases eq_one_or_eq_of_mem_zpowers htt hc with h | h
  · exfalso
    apply hnτ
    calc n * τ = (n * τ * n⁻¹ * τ⁻¹) * (τ * n) := by group
      _ = τ * n := by rw [h, one_mul]
  · calc n * τ * n⁻¹ = (n * τ * n⁻¹ * τ⁻¹) * τ := by group
      _ = t * τ := by rw [h]
      _ = τ * t := Lbar_comm S H.conj_mem ht hτA.1

theorem hkey_of_hsub (D : Std H C ht ht1 hVQ)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) :
    ∀ τ ∈ S9.conjL S g t, τ ≠ t → ∃ y ∈ Nbar S g t, y * τ * y⁻¹ = τ * t := by
  rintro τ ⟨hτL, x, hxM, rfl⟩ hτt
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  refine exists_Nbar_conj_eq_mul_of_mem_Abar D ⟨hτL, hsub x hxM hτL⟩ fun hz => ?_
  rcases eq_one_or_eq_of_mem_zpowers htt hz with h | h
  · apply ht1
    have := congrArg (fun y => x⁻¹ * y * x) h
    simpa [mul_assoc] using this
  · exact hτt h

theorem conjL_subset_Nbar
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) :
    S9.conjL S g t ⊆ Nbar S g t := by
  rintro τ ⟨hτL, x, hxM, rfl⟩
  exact hsub x hxM hτL

end CFSG.LargeExtraspecial.S8
