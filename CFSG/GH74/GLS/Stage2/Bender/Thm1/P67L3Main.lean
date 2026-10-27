module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Heis
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnFieldAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnChar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section Main

variable {K : Type} [Field K] [Finite K]

theorem cf67Deriv_L3_ne {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hrp : r ≠ p) {V Z : Subgroup (MulAut (projectiveSL 3 K))}
    (h2 : N2Cfg (projectiveSL 3 K) r V Z) (h3 : N3Deriv (projectiveSL 3 K) V Z) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  obtain ⟨hr, hrodd, hVe, hVc, -, -, -, -, -⟩ := id h2
  have hr2 : r ≠ 2 := by rintro rfl; exact absurd hrodd (by decide)
  have hrK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  by_cases hVD : V ≤ linearAutGroup 3 K
  · have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
      have := hVe
      exact setLike_mul_comm hx hy
    have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
    have h2K : (2 : K) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff K p] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    rw [linearAutGroup_eq_range] at hVD
    rcases inner_plane_classify hr hr2 hrK V hVD hVc hVe' hVab with ⟨B, hB⟩ | ⟨rfl, a, b, u, hu, ha, hb, hab, -⟩
    · exact false_of_toral_deriv h2 h3 h2K B (fun v hv => by
        obtain ⟨x, d, hx, hxd⟩ := hB v hv
        exact ⟨x, d, hx, hxd⟩)
    · have hp5 : 5 ≤ p := by
        have h2p := hp.two_le
        have h3p : p ≠ 3 := fun h => hrp h.symm
        have h4p : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        omega
      exact false_of_heis hp hp5 hf hK h2 h3 (by rw [linearAutGroup_eq_range]; exact hVD) a b u hu ha hb hab
  · exact false_of_noninner (le_refl 3) hp hf hK hrp h2 h3 hVD

end Main

theorem exists_L3_model {Y : Type} [Group Y] (hY : FL3 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Nat.card K = p ^ f ∧ Nonempty (Y ≃* projectiveSL 3 K) := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  exact ⟨K, inferInstance, inferInstance, p, f, hp, hp2, hf, hK, ⟨e⟩⟩

theorem cf67CoreFull_L3 (Y : Type) [Group Y] [Finite Y] (hY : FL3 Y) : CF67CoreFull Y := by
  obtain ⟨K, _, _, p, f, hp, hp2, hf, hK, ⟨e⟩⟩ := exists_L3_model hY
  refine CF67CoreFull.of_mulEquiv e ?_
  intro hs hn r V Z h2 h3
  by_cases hrp : r = p
  · subst hrp
    have : Fact r.Prime := ⟨hp⟩
    have : CharP K r := finite_field_prime_power_characteristic hp hf hK
    exact cf67_Ln_char (le_refl 3) r hp2
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)) h2 h3
  · exact cf67Deriv_L3_ne hp hp2 hf hK hrp h2 h3.deriv

theorem cf67CoreDeriv_L3_ne (Y : Type) [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hLie : Blueprint.LieModel Y .PSL 3 p f) {r : ℕ} (hrp : r ≠ p) :
    CF67CoreDeriv Y r := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  refine CF67CoreDeriv.of_mulEquiv e ?_
  intro hs hn V Z h2 h3
  exact cf67Deriv_L3_ne hp hp2 hf hK hrp h2 h3

theorem L3_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL3 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) :
    r = 3 ∧ ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ Blueprint.LieModel (J ⧸ center J) .PSL 3 p f ∧
      3 ∣ p ^ f - 1 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  have hM : Models.LieModel (J ⧸ center J) .PSL 3 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := by
    unfold genericOrders; rfl
  have hex : exceptionalOrders .PSL 3 p f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hpos : 0 < Nat.gcd 3 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : (genericOrders .PSL 3 p f).1 * (genericOrders .PSL 3 p f).2 *
      ((exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2) ≠ 0 := by
    rw [hex, hgen]; simp
  have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
  rw [hex, hgen] at h
  have h1 : r ∣ Nat.gcd 3 (p ^ f - 1) := by simpa using h
  have hr3 : r = 3 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h1.trans (Nat.gcd_dvd_left _ _))
  refine ⟨hr3, p, f, hp, hf, hp2, hLie, ?_⟩
  rw [← hr3]
  exact h1.trans (Nat.gcd_dvd_right _ _)

theorem cf67CoreDeriv_L3_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL3 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) : CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨rfl, p, f, hp, hf, hp2, hLie, h3d⟩ := L3_cover_odd hGA hJ hY hr hd
  have hrp : (3 : ℕ) ≠ p := by
    rintro rfl
    have h31 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 3 ^ f - (3 ^ f - 1) = 1 := by
      have := Nat.one_le_pow f 3 (by norm_num)
      omega
    have := Nat.dvd_sub h31 h3d
    rw [h1] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
  exact cf67CoreDeriv_L3_ne _ hp hp2 hf hLie hrp

theorem cf67L3_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67L3 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_L3 Y hY)
    (fun _ _ _ hJ hY _ hr _ hd => cf67CoreDeriv_L3_cover hGA hJ hY hr hd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
