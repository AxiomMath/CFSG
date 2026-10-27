module

public import CFSG.GH74.Uniqueness.SU.KI1r4TG1
public import CFSG.GH74.Uniqueness.SU.KI1r4QSw
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K
open CFSG.GH74.Uniqueness.SU.K.R4.Q64 CFSG.GH74.Uniqueness.SU.SU5
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem gf_facts (R : Subgroup H) (hF : generalizedFitting H = R) :
    R.Normal ∧ centralizer (R : Set H) ≤ R ∧
      ∀ W : Subgroup H, W ≤ normalizer (R : Set H) → IsPGroup 2 W →
        (∀ n ∈ normalizer (R : Set H), ∀ w ∈ W, n * w * n⁻¹ ∈ W) → W ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : R.Normal := hF ▸ (CFSG.LocalCores.generalized_fitting_characteristic).2
  refine ⟨hRn, ?_, ?_⟩
  · have := centralizer_generalizedFitting_le H
    rw [hF] at this
    exact this
  · intro W _ hW2 hWn
    have hWnormal : W.Normal := ⟨fun w hw g => hWn g
      (Subgroup.normalizer_eq_top_iff.mpr hRn ▸ Subgroup.mem_top g) w hw⟩
    have hle : W ≤ CFSG.pCore 2 H :=
      le_sSup (show W ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} from ⟨hWnormal, hW2⟩)
    refine hle.trans ((CFSG.pCore_le_fitting H 2).trans ?_)
    rw [← hF]
    exact le_sup_left

omit [Finite H] in
theorem mem_ZP_iff {T : Sylow 2 H} (g : H) :
    g ∈ ZP H T ↔ g ∈ Psub H T ∧ ∀ h ∈ Psub H T, g * h = h * g := by
  unfold ZP
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨h, hh⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_center_iff.mpr fun h => ?_, rfl⟩
    exact Subtype.ext (hc h h.2).symm

theorem q64_main
    {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H} (hR : RData T x A R y)
    (hF : generalizedFitting H = R) (hL : IsL34Type ↥R)
    (hQ8 : Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) :
    J2Structure H T := by
  classical
  obtain ⟨hRn, hC, hO2⟩ := gf_facts R hF
  have := hRn
  have := hR.A_normal
  have hRN : normalizer (R : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hRn
  have hRT : R ≤ (T : Subgroup H) := by rw [hR.R_eq]; exact inf_le_left
  have hR82 := hR.lemma82 le_rfl hR.x_norm hR.y_norm
  unfold Lemma82Concl at hR82
  obtain ⟨-, hZ4, hfr, -, hcom, -, -⟩ : (Nat.card R = 64 ∧ Nat.card (center ↥R) = 4 ∧
      frattini ↥R = center ↥R ∧ (∀ u : ↥R, u * u ∈ center ↥R) ∧
      (∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) ∧ (∀ a ∈ center ↥R, a * a = 1) ∧
      Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) := by
    rcases hR82 with ⟨hab, -⟩ | hb
    · exact absurd hab (not_abelian_of_isL34Type hL)
    · exact hb
  have hΦ4 : Nat.card (frattini ↥R) = 4 := by rw [hfr]; exact hZ4
  obtain ⟨U₁, U₂, hFa⟩ := hL.facts
  have hy3R : y ^ 3 ∈ R := hC (Subgroup.mem_centralizer_iff.mpr fun r hr =>
    (mul_inv_eq_iff_eq_mul.mp (hR.y_cube r hr)).symm)
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_mem_two_group R hR.R_two y hR.y_three hy3R
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : A = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact Subgroup.mem_bot.mpr (hno g hg)
    have h4 := hR.A_card
    rw [this, Subgroup.card_bot] at h4
    omega
  have hy1 : y ≠ 1 := by
    intro h
    exact hR.y_A a₀ ha₀A ha₀1 (by rw [h]; simp)
  have hxP : ∀ p, p ∈ R ↔ x * p * x⁻¹ ∈ R :=
    mem_iff_conj_of_involution R x hR.x_sq hR.x_norm
  have hTcard : Nat.card ↥(T : Subgroup H) = 2 * Nat.card R := by
    rw [hR.T_eq, sup_comm]
    exact card_sup_zpowers R x hR.x_sq hxP hR.x_not_mem
  have hodd : ∀ P : Subgroup H, ¬ 2 ∣ Nat.card P → Nat.card P ∣ 9 := fun P hP =>
    card_odd_dvd_nine hFa hR.R_two hC hO2 hfr hΦ4 P (hRN ▸ le_top) hP
  obtain ⟨P₃, x', hP3, hyP, hP39, hGcard, hRP, hx'2, hx'R, hx'K, hx'P, hx'y, r, hr, hx'r⟩ :=
    exists_sylow_data R hR.R_two T hTcard x y hR.x_sq hR.x_not_mem hy3 hy1 hR.xy hR.y_free hodd
  have hU₁ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₁ := fun z hz => (frattini_mem hFa hfr z hz).1
  have hU₂ : ∀ z ∈ frattini ↥R, (z : H) ∈ U₂ := fun z hz => (frattini_mem hFa hfr z hz).2
  have hswap := swap_of_quaternion hFa x hR.x_sq hR.x_norm hQ8
  have hswap' : ∀ u : H, u ∈ U₁ ↔ x' * u * x'⁻¹ ∈ U₂ := by
    rw [hx'r]
    exact swap_of_mul hFa.B_le hcom (fun z hz => hU₂ z (hfr ▸ hz)) hswap hr
  have hnot : Nat.card P₃ = 9 → ∃ p ∈ P₃, x' * p * x'⁻¹ ≠ p⁻¹ := by
    intro hP9
    have hodd9 : ¬ 2 ∣ Nat.card P₃ := by rw [hP9]; norm_num
    have hPN : P₃ ≤ normalizer (R : Set H) := hRN ▸ le_top
    have hQ9 := card_map_actV hR.R_two hC hO2 P₃ hPN hodd9
    rw [hP9] at hQ9
    have hE₁ : Nat.card U₁ = 16 := by have := hFa.A_E.2; norm_num at this; exact this
    have hV₁ : Nat.card (imV R U₁) = 4 := card_imV_eq_four hFa.A_le hE₁ hΦ4 hU₁
    have hsup := imV_sup hFa.A_le hFa.B_le hFa.sup_eq
    have hx'N : x' ∈ normalizer (R : Set H) := hRN ▸ Subgroup.mem_top x'
    obtain ⟨φ, hφ, hne⟩ := not_all_inverted (imV R U₁) (imV R U₂) hV₁ hsup _ hQ9
      (fun φ hφ v => (actV_preserves_of_odd hFa hU₁ hU₂ P₃ hodd9 φ hφ v).1)
      (actV R ⟨x', hx'N⟩) (fun v => actV_mem_iff R U₁ U₂ hU₁ hU₂ ⟨x', hx'N⟩ hswap' v)
    obtain ⟨g, hg, rfl⟩ := hφ
    refine ⟨(g : H), hg, fun h => hne ?_⟩
    have h1 : (⟨x', hx'N⟩ : ↥(normalizer (R : Set H))) * g * (⟨x', hx'N⟩ : ↥(normalizer (R : Set H)))⁻¹
        = g⁻¹ := Subtype.ext h
    have h2 : actV R ((⟨x', hx'N⟩ : ↥(normalizer (R : Set H))) * g *
        (⟨x', hx'N⟩ : ↥(normalizer (R : Set H)))⁻¹) = (actV R g)⁻¹ := by rw [h1, map_inv]
    rw [map_mul, map_mul, map_inv] at h2
    exact h2
  have hxn : x' ∉ P₃ := fun h => hx'K (Subgroup.mem_sup_right h)
  obtain ⟨E, E₀, hEdef, hE₀def, hE₀E, hEcard, hE₀S3, hES, hEK, hE₀K, hcomm, hKcard, hord3⟩ :=
    exists_E_structure A P₃ hR.A_card hP39 x' y hx'2 hxn hyP hy3 hx'P hx'y hR.y_A hnot
  have hRE : R ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzR, hzE⟩
    rw [hEdef] at hzE
    rcases mem_sup_zpowers_or P₃ x' hx'2 hx'P hzE with hz | ⟨p, hp, rfl⟩
    · have : z ∈ R ⊓ P₃ := ⟨hzR, hz⟩
      rw [hRP] at this
      exact this
    · exfalso
      apply hx'K
      have : x' = (x' * p) * p⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hzR) (Subgroup.mem_sup_right (P₃.inv_mem hp))
  have hRE_top : R ⊔ E = ⊤ := by
    have h1 := card_mul_le_card_sup R E hRE
    have h2 : Nat.card ↥(R ⊔ E) ≤ Nat.card H := Subgroup.card_le_card_group _
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm h2
    calc Nat.card H = 2 * Nat.card R * Nat.card P₃ := hGcard
      _ = Nat.card R * Nat.card E := by rw [hEcard]; ring
      _ ≤ Nat.card ↥(R ⊔ E) := h1
  have hPsub : Psub H T = R := by
    unfold Psub
    rw [hF]
    exact inf_eq_right.mpr hRT
  have hAZ : A = Zc R := by
    have hle : A ≤ Zc R := by
      intro g hg
      rw [mem_Zc]
      refine ⟨hR.A_le hg, fun h hh => ?_⟩
      have hh' : h ∈ centralizer (A : Set H) := by
        have : h ∈ (T : Subgroup H) ⊓ centralizer (A : Set H) := hR.R_eq ▸ hh
        exact this.2
      exact Subgroup.mem_centralizer_iff.mp hh' g hg
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h4 := hFa.Z_E.2
    rw [hR.A_card]
    norm_num at h4
    omega
  have hZP : ZP H T = A := by
    ext g
    rw [mem_ZP_iff, hPsub, hAZ, mem_Zc]
  have hx'T : x ∈ (T : Subgroup H) := hR.T_eq ▸ Subgroup.mem_sup_right (mem_zpowers x)
  refine ⟨isJ2Type_of_extension (T : Subgroup H) R x hRT hx'T hR.x_sq hR.x_not_mem hR.x_norm
      hR.T_eq hL hQ8, ?_, E, ?_, ?_, hES, E₀, hE₀E, hE₀S3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPsub]; exact hL
  · rw [hPsub, hRN]; exact hRE_top.symm
  · rw [hPsub]; exact hRE
  · rw [hZP]; exact hEK
  · rw [hZP]; exact hE₀K
  · rw [hZP]; exact hcomm
  · intro a ha ha3 t ht hat
    rw [hPsub] at ht
    have hay : a ∈ zpowers y := hord3 a ha ha3
    have hy3o : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hzz : zpowers a = zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hay) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hy3o]
    have hya : y ∈ zpowers a := hzz ▸ mem_zpowers y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hya
    have hcm : Commute a t := by
      have : a * t = t * a := by
        have := hat
        exact mul_inv_eq_iff_eq_mul.mp this
      exact this
    have hyt : y * t * y⁻¹ = t := by
      rw [← hk]
      have := (Commute.zpow_left hcm k)
      exact mul_inv_eq_iff_eq_mul.mpr this
    exact hR.y_free t ht hyt
  · rw [hZP]; exact hKcard

end CFSG.GH74.Uniqueness.SU.K.R4
