module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnInner
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE2Five
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L5Heis
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnChar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnFieldAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section L5

variable {K : Type} [Field K] [Finite K]

theorem three_pow_contra {f : ℕ} (h4 : 3 ^ f % 4 = 3) (h5 : 5 ∣ 3 ^ f - 1) : False := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b : ℕ, b < 4 ∧ f = 4 * a + b := ⟨f / 4, f % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have h81 : 3 ^ (4 * a + b) = 81 ^ a * 3 ^ b := by
    rw [pow_add, pow_mul]; norm_num
  have h20 : 81 ^ a % 20 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have h1 : 3 ^ (4 * a + b) % 20 = 3 ^ b % 20 := by
    rw [h81, Nat.mul_mod, h20]; simp
  have hpos : 1 ≤ 3 ^ (4 * a + b) := Nat.one_le_pow _ _ (by norm_num)
  have h5' : 3 ^ (4 * a + b) % 5 = 1 := by omega
  interval_cases b <;> omega

theorem false_of_inner_L5 {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hq4 : p ^ f % 4 = 3) (hrp : r ≠ p) {V Z : Subgroup (MulAut (projectiveSL 5 K))}
    (h2 : N2Cfg (projectiveSL 5 K) r V Z) (h3 : N3Full (projectiveSL 5 K) V Z)
    (hVI : V ≤ linearAutGroup 5 K) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hr, hr2, -⟩ := id h2
  have : Fact r.Prime := ⟨hr⟩
  have hrK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  have hVD : ∀ v ∈ V, ∃ A : GL (Fin 5) K, v = conjAut 5 K A := by
    intro v hv
    have := hVI hv
    rw [linearAutGroup_eq_range] at this
    obtain ⟨A, hA⟩ := this
    exact ⟨A, hA.symm⟩
  refine false_of_inner_Ln45 (Or.inr rfl) hr2 hrK h2 hVD (fun hA => ?_) (fun hrq => ?_)
  · by_cases h5 : r = 5
    · subst h5
      have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      have hp3 : p ≠ 3 := by
        rintro rfl
        rw [hK] at hA
        exact three_pow_contra hq4 hA
      have hp7 : 7 ≤ p := by
        have h2p := hp.two_le
        have h4p : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        have h6p : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
        omega
      exact false_of_e1_five hp hp7 hf hK hA h2 h3.deriv hVI
    · have hcop : Nat.Coprime 5 r := (Nat.coprime_primes Nat.prime_five hr).mpr (Ne.symm h5)
      exact false_of_e1_cop (by norm_num) hcop hA h2 h3 hVI
  · exact Ln.E2.false_of_e2_five p hr2 hrq h2 h3 hVD

end L5

section L5Main

theorem exists_L5_model {Y : Type} [Group Y] (hY : FL5 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
      Nat.card K = p ^ f ∧ Nonempty (Y ≃* projectiveSL 5 K) := by
  obtain ⟨p, f, hp, hf, hq4, hLie⟩ := hY
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  exact ⟨K, inferInstance, inferInstance, p, f, hp, hp2, hf, hq4, hK, ⟨e⟩⟩

theorem cf67CoreFull_L5 (Y : Type) [Group Y] [Finite Y] (hY : FL5 Y) : CF67CoreFull Y := by
  obtain ⟨K, _, _, p, f, hp, hp2, hf, hq4, hK, ⟨e⟩⟩ := exists_L5_model hY
  refine CF67CoreFull.of_mulEquiv e ?_
  intro hs hn r V Z h2 h3
  by_cases hrp : r = p
  · subst hrp
    have : Fact r.Prime := ⟨hp⟩
    have : CharP K r := finite_field_prime_power_characteristic hp hf hK
    exact cf67_Ln_char (by norm_num) r hp2
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)) h2 h3
  · by_cases hVD : V ≤ linearAutGroup 5 K
    · exact false_of_inner_L5 hp hf hK hq4 hrp h2 h3 hVD
    · exact false_of_noninner (by norm_num) hp hf hK hrp h2 h3.deriv hVD

theorem cf67CoreDeriv_L5_five (Y : Type) [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq4 : p ^ f % 4 = 3) (h5 : 5 ∣ p ^ f - 1) (hLie : Blueprint.LieModel Y .PSL 5 p f) :
    CF67CoreDeriv Y 5 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  refine CF67CoreDeriv.of_mulEquiv e ?_
  intro hs hn V Z h2 h3
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact three_pow_contra hq4 h5
  have hp5 : p ≠ 5 := by
    rintro rfl
    have h1 : 5 ∣ 5 ^ f := dvd_pow_self 5 (by omega)
    have h2' : 5 ^ f - (5 ^ f - 1) = 1 := by
      have := Nat.one_le_pow f 5 (by norm_num)
      omega
    have := Nat.dvd_sub h1 h5
    rw [h2'] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
  have hp7 : 7 ≤ p := by
    have h2p := hp.two_le
    have h4p : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    have h6p : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
    omega
  by_cases hVD : V ≤ linearAutGroup 5 K
  · exact false_of_e1_five hp hp7 hf hK (by rw [hK]; exact h5) h2 h3 hVD
  · exact false_of_noninner (by norm_num) hp hf hK (Ne.symm hp5) h2 h3 hVD

theorem L5_cover_odd (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL5 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) :
    r = 5 ∧ ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ Blueprint.LieModel (J ⧸ center J) .PSL 5 p f ∧
      5 ∣ p ^ f - 1 := by
  obtain ⟨p, f, hp, hf, hq4, hLie⟩ := hY
  have hM : Models.LieModel (J ⧸ center J) .PSL 5 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := by
    unfold genericOrders; rfl
  have hex : exceptionalOrders .PSL 5 p f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hpos : 0 < Nat.gcd 5 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : (genericOrders .PSL 5 p f).1 * (genericOrders .PSL 5 p f).2 *
      ((exceptionalOrders .PSL 5 p f).1 * (exceptionalOrders .PSL 5 p f).2) ≠ 0 := by
    rw [hex, hgen]; simp
  have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
  rw [hex, hgen] at h
  have h1 : r ∣ Nat.gcd 5 (p ^ f - 1) := by simpa using h
  have hr5 : r = 5 :=
    (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp (h1.trans (Nat.gcd_dvd_left _ _))
  refine ⟨hr5, p, f, hp, hf, hq4, hLie, ?_⟩
  rw [← hr5]
  exact h1.trans (Nat.gcd_dvd_right _ _)

theorem cf67CoreDeriv_L5_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL5 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hd : r ∣ Nat.card (center J)) : CF67CoreDeriv (J ⧸ center J) r := by
  obtain ⟨rfl, p, f, hp, hf, hq4, hLie, h5⟩ := L5_cover_odd hGA hJ hY hr hd
  exact cf67CoreDeriv_L5_five _ hp hf hq4 h5 hLie

theorem cf67L5_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67L5 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_L5 Y hY)
    (fun _ _ _ hJ hY _ hr _ hd => cf67CoreDeriv_L5_cover hGA hJ hY hr hd)

end L5Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
