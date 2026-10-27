module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnInner
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnE2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnChar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnFieldAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section L4

variable {K : Type} [Field K] [Finite K]

theorem false_of_inner_L4 {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hrp : r ≠ p) {V Z : Subgroup (MulAut (projectiveSL 4 K))}
    (h2 : N2Cfg (projectiveSL 4 K) r V Z) (h3 : N3Full (projectiveSL 4 K) V Z)
    (hVI : V ≤ linearAutGroup 4 K) : False := by
  classical
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hr, hr2, -⟩ := id h2
  have : Fact r.Prime := ⟨hr⟩
  have hrK : ¬ r ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  have hVD : ∀ v ∈ V, ∃ A : GL (Fin 4) K, v = conjAut 4 K A := by
    intro v hv
    have := hVI hv
    rw [linearAutGroup_eq_range] at this
    obtain ⟨A, hA⟩ := this
    exact ⟨A, hA.symm⟩
  refine false_of_inner_Ln45 (Or.inl rfl) hr2 hrK h2 hVD (fun hA => ?_) (fun hrq => ?_)
  · have hcop2 : Nat.Coprime 2 r :=
      (Nat.coprime_primes Nat.prime_two hr).mpr (by rintro rfl; exact absurd hr2 (by decide))
    have hcop4 : Nat.Coprime 4 r := by simpa using hcop2.pow_left 2
    exact false_of_e1_cop (by norm_num) hcop4 hA h2 h3 hVI
  · exact Ln.E2.false_of_e2_four p hr2 hrq h2 h3 hVD

end L4

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.OddAut

section L4Main

theorem exists_L4_model {Y : Type} [Group Y] (hY : FL4 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Nat.card K = p ^ f ∧ Nonempty (Y ≃* projectiveSL 4 K) := by
  obtain ⟨p, f, hp, hf, hp2, -, hLie⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  exact ⟨K, inferInstance, inferInstance, p, f, hp, hp2, hf, hK, ⟨e⟩⟩

theorem cf67CoreFull_L4 (Y : Type) [Group Y] [Finite Y] (hY : FL4 Y) : CF67CoreFull Y := by
  obtain ⟨K, _, _, p, f, hp, hp2, hf, hK, ⟨e⟩⟩ := exists_L4_model hY
  refine CF67CoreFull.of_mulEquiv e ?_
  intro hs hn r V Z h2 h3
  by_cases hrp : r = p
  · subst hrp
    have : Fact r.Prime := ⟨hp⟩
    have : CharP K r := finite_field_prime_power_characteristic hp hf hK
    exact cf67_Ln_char (by norm_num) r hp2
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)) h2 h3
  · by_cases hVD : V ≤ linearAutGroup 4 K
    · exact false_of_inner_L4 hp hf hK hrp h2 h3 hVD
    · exact false_of_noninner (by norm_num) hp hf hK hrp h2 h3.deriv hVD

theorem L4_no_odd_cover (hGA : CFSG.Open.GriessAllModelsStatement)
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J) (hY : FL4 (J ⧸ center J)) {r : ℕ}
    (hr : r.Prime) (hr2 : Odd r) (hd : r ∣ Nat.card (center J)) : False := by
  obtain ⟨p, f, hp, hf, hp2, -, hLie⟩ := hY
  have hM : Models.LieModel (J ⧸ center J) .PSL 4 p f :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hLie
  have hgen : genericOrders .PSL 4 p f = (Nat.gcd 4 (p ^ f - 1), 1) := by
    unfold genericOrders; rfl
  have hex : exceptionalOrders .PSL 4 p f = (1, 1) := by
    unfold exceptionalOrders; split <;> simp_all
  have hpos : 0 < Nat.gcd 4 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne : (genericOrders .PSL 4 p f).1 * (genericOrders .PSL 4 p f).2 *
      ((exceptionalOrders .PSL 4 p f).1 * (exceptionalOrders .PSL 4 p f).2) ≠ 0 := by
    rw [hex, hgen]; simp
  have h := hd.trans (card_center_dvd_table hGA hJ hM hne)
  rw [hex, hgen] at h
  have h1 : r ∣ Nat.gcd 4 (p ^ f - 1) := by simpa using h
  have h4 : r ∣ 2 ^ 2 := by simpa using h1.trans (Nat.gcd_dvd_left _ _)
  have h2' : r ∣ 2 := hr.dvd_of_dvd_pow h4
  have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2'
  subst this
  exact absurd hr2 (by decide)

theorem cf67L4_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67L4 :=
  cf67Fam_of_core (fun Y _ _ hY => cf67CoreFull_L4 Y hY)
    (fun _ _ _ hJ hY _ hr hr2 hd => (L4_no_odd_cover hGA hJ hY hr hr2 hd).elim)

end L4Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
