module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Model
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Lift
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Toral
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3HeisCore
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnField

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag


section Main

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_ne_aux (hp2 : p ≠ 2) {r : ℕ} (hrp : r ≠ p)
    {V Z : Subgroup (MulAut (U3T h))} (h2 : N2Cfg (U3T h) r V Z) (h3 : N3Deriv (U3T h) V Z)
    (htoral : ∀ E : U3U h, (∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
        v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
          ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((E : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) = ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              Matrix.diagonal d) → False) : False := by
  classical
  have : Finite K := h.finite
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h4⟩
    have : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    rw [h4] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  by_cases hVD : V ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  · obtain ⟨hr, hrodd, hVe, hVc, -, -, -, -, -⟩ := id h2
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact absurd hrodd (by decide)
    have hrK : ¬ r ∣ Nat.card K := by
      rw [h.card]
      intro hd
      exact hrp ((Nat.prime_dvd_prime_iff_eq hr h.prime).1 (hr.dvd_of_dvd_pow hd))
    have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
      have := hVe
      exact setLike_mul_comm hx hy
    have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
    rcases u3_plane_classify h hr hr2 hrK V hVD hVc hVe' hVab with ⟨E, hE⟩ |
        ⟨rfl, a, b, u, hu, ha, hb, hab, -⟩
    · exact htoral E hE
    · have hp5 : 5 ≤ p := by
        have h2p := h.prime.two_le
        have h3p : p ≠ 3 := fun h' => hrp h'.symm
        have h4p : p ≠ 4 := by rintro rfl; exact absurd h.prime (by decide)
        omega
      exact false_of_u3_heis h hp5 h2 h3 a b u hu ha hb hab
  · exact false_of_u_noninner h (le_refl 3) hq hp2 hrp h2 h3 hVD

include h in
theorem u3_hq (hp2 : p ≠ 2) : ¬(3 = 3 ∧ p ^ f = 2) := by
  rintro ⟨-, h4⟩
  have : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
  rw [h4] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)

theorem cf67Full_U3_ne (hp2 : p ≠ 2) {r : ℕ} (hrp : r ≠ p) {V Z : Subgroup (MulAut (U3T h))}
    (h2 : N2Cfg (U3T h) r V Z) (h3 : N3Full (U3T h) V Z) : False := by
  have : Finite K := h.finite
  have hq := u3_hq h hp2
  have hTs := isSimpleGroup_primeFormP_one h (le_refl 3) hq
  have hTn : ∃ a b : U3T h, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h (le_refl 3) hq hcon
  exact u3_ne_aux h hp2 hrp h2 h3.deriv (fun E hE => false_of_u3_toral h hp2 hTs hTn h2 h3 E hE)

theorem cf67Deriv_U3_ne (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f) {r : ℕ} (hrp : r ≠ p)
    {V Z : Subgroup (MulAut (U3T h))} (h2 : N2Cfg (U3T h) r V Z) (h3 : N3Deriv (U3T h) V Z) :
    False := by
  have : Finite K := h.finite
  have hq := u3_hq h hp2
  have hTs := isSimpleGroup_primeFormP_one h (le_refl 3) hq
  have hTn : ∃ a b : U3T h, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h (le_refl 3) hq hcon
  exact u3_ne_aux h hp2 hrp h2 h3
    (fun E hE => false_of_u3_toral_deriv h hp2 h4 hTs hTn h2 h3 E hE)

end Main

theorem exists_U3_model {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hLie : LieModel Y .PSU 3 p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K), Nonempty (Y ≃* U3T h) := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq := u3_hq h hp2
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one (n := 3)) (le_refl 3) hq
  exact ⟨F, inferInstance, h, ⟨(e₀.trans (unitaryPSUEquiv h (by omega)).symm).trans eT.symm⟩⟩

theorem cf67CoreFull_U3 (Y : Type) [Group Y] [Finite Y] (hY : FU3 Y) : CF67CoreFull Y := by
  intro hs hn r V Z h2 h3
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  by_cases hrp : r = p
  · subst hrp
    exact cf67_U3_char_of_lieModel hp2 hLie hs hn h2 h3
  · obtain ⟨K, _, h, ⟨e⟩⟩ := exists_U3_model hp2 hLie
    exact cf67Full_U3_ne h hp2 hrp (h2.map_mulEquiv (MulAut.congr e)) (h3.map_mulEquiv e)

theorem U3_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FU3 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) :
    r = 3 ∧ ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ≠ 2 ∧ Blueprint.LieModel (J ⧸ center J) .PSU 3 p f ∧
      3 ∣ p ^ f + 1 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  have hM : Models.LieModel (J ⧸ center J) .PSU 3 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := by
    unfold genericOrders; rfl
  have hex : exceptionalOrders .PSU 3 p f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hpos : 0 < Nat.gcd 3 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : (genericOrders .PSU 3 p f).1 * (genericOrders .PSU 3 p f).2 *
      ((exceptionalOrders .PSU 3 p f).1 * (exceptionalOrders .PSU 3 p f).2) ≠ 0 := by
    rw [hex, hgen]; simp
  have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
  rw [hex, hgen] at h
  have h1 : r ∣ Nat.gcd 3 (p ^ f + 1) := by simpa using h
  have hr3 : r = 3 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (h1.trans (Nat.gcd_dvd_left _ _))
  refine ⟨hr3, p, f, hp, hf, hp2, hLie, ?_⟩
  rw [← hr3]
  exact h1.trans (Nat.gcd_dvd_right _ _)

theorem cf67CoreDeriv_U3_cover
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FU3 (J ⧸ center J))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card (center J)) : CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨rfl, p, f, hp, hf, hp2, hLie, h3d⟩ := U3_cover_odd hGA hJ hY hr hd
  have hrp : (3 : ℕ) ≠ p := by
    rintro rfl
    have h31 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 3 ^ f + 1 - 3 ^ f = 1 := by omega
    have := Nat.dvd_sub h3d h31
    rw [h1] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
  have h4 : 4 ≤ p ^ f := by
    have h1 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h3p : 3 ≤ p := by have := hp.two_le; omega
    omega
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_U3_model hp2 hLie
  have : Finite K := h.finite
  exact CF67CoreDeriv.of_mulEquiv e (fun _ _ V Z h2 h3 => cf67Deriv_U3_ne h hp2 h4 hrp h2 h3)

theorem cf67U3_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67U3 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_U3 Y hY)
    (fun _ _ _ hJ hY _ hr _ hd => cf67CoreDeriv_U3_cover hGA hJ hY hr hd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
