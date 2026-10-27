module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.CentralExt.GriessClassical
open scoped MatrixGroups

private theorem exceptionalOrders_PSU_two_le (d n : ℕ) :
    (exceptionalOrders .PSU d 2 n).1 ≤ 2 ∧ (exceptionalOrders .PSU d 2 n).2 ≤ 2 ∧
      1 ≤ (exceptionalOrders .PSU d 2 n).1 ∧ 1 ≤ (exceptionalOrders .PSU d 2 n).2 := by
  unfold exceptionalOrders
  split <;> simp_all

private theorem card_generic_exceptional_PSU (d n : ℕ) :
    Nat.card (generic .PSU d 2 n × exceptional .PSU d 2 n) =
      (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 *
        ((exceptionalOrders .PSU d 2 n).1 * (exceptionalOrders .PSU d 2 n).2) := by
  simp only [generic, exceptional, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

private theorem not_dvd_psu_orders {p d n : ℕ} (hp : p.Prime) (hd : ¬ p ∣ d)
    (hpdvd : p ∣ 2 ^ n + 1) (hn1 : 1 ≤ n) (hd3 : 3 ≤ d) :
    ¬ p ∣ (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 *
      ((exceptionalOrders .PSU d 2 n).1 * (exceptionalOrders .PSU d 2 n).2) := by
  intro h
  obtain ⟨he1, he2, he1', he2'⟩ := exceptionalOrders_PSU_two_le d n
  have hp3 : 3 ≤ p := by
    have hpne : p ≠ 2 := by
      intro h2
      subst h2
      have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have : 2 ∣ 1 := (Nat.dvd_add_iff_right h2n).mpr hpdvd
      norm_num at this
    have := hp.two_le
    omega
  have hgen : (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 =
      Nat.gcd d (2 ^ n + 1) := by
    simp [genericOrders]
  rw [hgen] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
  · exact hd (h1.trans (Nat.gcd_dvd_left d (2 ^ n + 1)))
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h4
    · have := Nat.le_of_dvd (by omega) h3
      omega
    · have := Nat.le_of_dvd (by omega) h4
      omega

private theorem center_dvd_of_psu_row {K X : Type} [Group K] [Finite K] [Group X]
    (hK : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X) {d n : ℕ}
    (hrow : commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
      generic .PSU d 2 n × exceptional .PSU d 2 n)) :
    Nat.card (Subgroup.center K) ∣
      (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 *
        ((exceptionalOrders .PSU d 2 n).1 * (exceptionalOrders .PSU d 2 n).2) := by
  have h := card_center_dvd_hopfMultiplier_of_cover hK
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by simp)
  obtain ⟨-, ⟨r⟩⟩ := hrow
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
    Nat.card_congr r.toEquiv, card_generic_exceptional_PSU] at h
  exact h

theorem uni_center_coprime
    {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} (hS : CFSG.Open.IsQuasisimple ↥S) {n d : ℕ} {F : Type} [Field F]
    [Finite F] {θ : ↥S ⧸ Subgroup.center ↥S ≃* UniPSU n d F} (hM : UniMarking p S B n d F θ)
    (hd : ¬ p ∣ d) : ¬ p ∣ Nat.card (Subgroup.center ↥S) := by
  have hFcard : Nat.card F = (2 ^ n) ^ 2 := hM.1
  have hn1 : 1 ≤ n := hM.2.1
  have hd3 : 3 ≤ d := hM.2.2.1
  have hd3n : d = 3 → 2 ≤ n := hM.2.2.2.1
  have hpdvd : p ∣ 2 ^ n + 1 := hM.2.2.2.2.1
  have hadm : StatedLieAdmissible .PSU d 2 n := by
    refine ⟨Nat.prime_two, hn1, hd3, ?_⟩
    rw [ne_eq, Prod.mk.injEq, not_and]
    intro hd3' h2n
    have hn2 : 2 ≤ n := hd3n hd3'
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hn2
    omega
  have hmodel : StatedClassicalModel (UniPSU n d F) .PSU d 2 n :=
    CFSG.StandardType.statedClassicalModel_unitary d n hFcard hadm
  have hnot : ¬ p ∣ (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 *
      ((exceptionalOrders .PSU d 2 n).1 * (exceptionalOrders .PSU d 2 n).2) :=
    not_dvd_psu_orders hp hd hpdvd hn1 hd3
  have hcenter : Nat.card (Subgroup.center ↥S) ∣
      (genericOrders .PSU d 2 n).1 * (genericOrders .PSU d 2 n).2 *
        ((exceptionalOrders .PSU d 2 n).1 * (exceptionalOrders .PSU d 2 n).2) := by
    by_cases hdodd : Even d
    · by_cases hn2 : 2 ≤ n
      · have hq : 4 ≤ 2 ^ n ∨ (2 ^ n = 2 ∧ 8 ≤ d) ∨ (2 ^ n = 3 ∧ 6 ≤ d) := by
          left
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hn2
        exact center_dvd_of_psu_row hS θ (psu_row (X := UniPSU n d F) (n := d) (p := 2)
          (f := n) hmodel hdodd hq)
      · have hn_eq : n = 1 := by omega
        subst hn_eq
        by_cases hd4 : d = 4
        · subst hd4
          have hmodel4 : CFSG.Models.LieModel (UniPSU 1 4 F) .PSU 4 2 1 :=
            ⟨hadm, Or.inl hmodel⟩
          exact center_dvd_of_psu_row hS θ
            (psu_four_two_row (X := UniPSU 1 4 F) hmodel4)
        · have hd8 : 8 ≤ d := by
            rcases Nat.lt_or_ge d 8 with hlt | hge
            · exfalso
              have h6 : 6 ≤ d := by
                rcases hdodd with ⟨k, hk⟩
                omega
              have hne6 : d ≠ 6 := by
                rintro rfl
                have hp3 : p = 3 := by
                  have h : p ∣ 3 := by simpa using hpdvd
                  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
                exact hd (by rw [hp3]; norm_num)
              rcases hdodd with ⟨k, hk⟩
              omega
            · exact hge
          have hq : 4 ≤ 2 ^ 1 ∨ (2 ^ 1 = 2 ∧ 8 ≤ d) ∨ (2 ^ 1 = 3 ∧ 6 ≤ d) :=
            Or.inr (Or.inl ⟨by norm_num, hd8⟩)
          exact center_dvd_of_psu_row hS θ (psu_row (X := UniPSU 1 d F) (n := d) (p := 2)
            (f := 1) hmodel hdodd hq)
    · exact center_dvd_of_psu_row hS θ
        (psu_odd_row (X := UniPSU n d F) (n := d) (p := 2) (f := n) hmodel hdodd)
  intro hpZ
  exact hnot (hpZ.trans hcenter)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
