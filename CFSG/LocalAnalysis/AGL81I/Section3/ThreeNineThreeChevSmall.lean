module

import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeSmall
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_of_orders {a c q s : ℕ} (h : ThreeNineHyp K E D X₁ 3 d)
    (hZ : Subgroup.center ↥K = ⊥) (hOut : Nat.card (Outer ↥K) ∣ 2 ^ s) (hq : q.Prime)
    (hcard : Nat.card ↥K = 2 ^ a * 3 ^ c * q)
    (hkey : ∀ m ∈ Nat.divisors (2 ^ a), m ≡ 1 [MOD 3] → m ≡ 1 [MOD q] → m = 1) : False := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hd2 : ¬ d ∣ 2 := fun hd =>
    h.d_ne_two ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp hd)
  have hd3 : ¬ d ∣ 3 := fun hd =>
    h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp hd)
  have h32 : ¬ 3 ∣ 2 := by norm_num
  have hout3 : ¬ 3 ∣ Nat.card (Outer ↥K) := fun h3 =>
    h32 (Nat.prime_three.dvd_of_dvd_pow (h3.trans hOut))
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd =>
    hd2 (h.d_prime.dvd_of_dvd_pow (hd.trans hOut))
  obtain ⟨hY, hm3, hmd, h3Y, hdY, hdK⟩ := h.index_facts hZ hout3 houtd
  rw [hcard] at h3Y hdY hdK
  have hdq : d = q := by
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · exact absurd (h.d_prime.dvd_of_dvd_pow h1) hd2
      · exact absurd (h.d_prime.dvd_of_dvd_pow h1) hd3
    · exact (Nat.prime_dvd_prime_iff_eq h.d_prime hq).mp h1
  subst hdq
  have h3k : ¬ 3 ∣ 2 ^ a * d := fun h1 => by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h1 | h1
    · exact h32 (Nat.prime_three.dvd_of_dvd_pow h1)
    · exact h.d_ne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.d_prime).mp h1).symm
  have hdk : ¬ d ∣ 2 ^ a * 3 ^ c := fun h1 => by
    rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
    · exact hd2 (h.d_prime.dvd_of_dvd_pow h1)
    · exact hd3 (h.d_prime.dvd_of_dvd_pow h1)
  have h3 : 3 ^ (2 ^ a * 3 ^ c * d).factorization 3 = 3 ^ c :=
    (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := c)
      (k := 2 ^ a * d) (N := 2 ^ a * 3 ^ c * d) (by ring) h3k).symm
  have hd1 : d ^ (2 ^ a * 3 ^ c * d).factorization d = d := by
    have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := d) (a := 1)
      (k := 2 ^ a * 3 ^ c) (N := 2 ^ a * 3 ^ c * d) (by ring) hdk).symm
    rwa [pow_one] at this
  rw [h3] at h3Y
  rw [hd1] at hdY
  have hcop : Nat.Coprime (3 ^ c) d :=
    Nat.Coprime.pow_left c ((Nat.coprime_primes Nat.prime_three h.d_prime).mpr (Ne.symm h.d_ne))
  have h3d : 3 ^ c * d ∣ Nat.card (X₁.subgroupOf K) := hcop.mul_dvd_of_dvd_of_dvd h3Y hdY
  have hidx := index_dvd_div_of_dvd_card h3d
  have hpos : 0 < 3 ^ c * d := Nat.mul_pos (pow_pos (by norm_num) c) h.d_prime.pos
  rw [hcard, mul_assoc, Nat.mul_div_cancel _ hpos] at hidx
  have h1 := hkey _ (Nat.mem_divisors.mpr ⟨hidx, (pow_pos (by norm_num) a).ne'⟩) hm3 hmd
  exact hY (Subgroup.index_eq_one.mp h1)

private theorem center_eq_bot_of_simple_of_not_prime {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ :=
  TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => by
    have := hc
    exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem false_of_threeNineHyp_L33 (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : IsPSLType 3 (ZMod 3) ↥K) : False := by
  obtain ⟨e⟩ := hK
  have hm : StatedClassicalModel ↥K .PSL 3 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩, ZMod 3, inferInstance,
      inferInstance, by simp,
      ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 3))⟩⟩
  have hcard : Nat.card ↥K = 5616 := StatedAPI.card_of_statedClassicalModel_psl_three_three hm
  have : IsSimpleGroup ↥K := StatedAPI.isSimpleGroup_of_statedClassicalModel hm
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (by rw [hcard]; norm_num)
  have hOut : Nat.card (Outer ↥K) ∣ 2 ^ 1 := by
    have := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) le_rfl Nat.prime_three le_rfl hm).1
    simpa [CFSG.RankThree.OuterOrder.determinantParameter] using this
  exact false_of_threeNineHyp_of_orders (a := 4) (c := 3) (q := 13) h hZ hOut (by norm_num)
    (hcard.trans (by norm_num)) (by decide)

theorem false_of_threeNineHyp_U33 (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSU 3 3 1) : False := by
  have hcard : Nat.card ↥K = 6048 := StatedAPI.card_of_statedClassicalModel_psu_three_three hK
  have : IsSimpleGroup ↥K := StatedAPI.isSimpleGroup_of_statedClassicalModel hK
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (by rw [hcard]; norm_num)
  have hOut : Nat.card (Outer ↥K) ∣ 2 ^ 1 := by
    have := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_three le_rfl hK).1
    simpa [CFSG.RankThree.OuterOrder.determinantParameter] using this
  exact false_of_threeNineHyp_of_orders (a := 5) (c := 3) (q := 7) h hZ hOut (by norm_num)
    (hcard.trans (by norm_num)) (by decide)

theorem false_of_threeNineHyp_L29 (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSL 2 3 2) : False := by
  obtain ⟨φ⟩ := StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hK
  exact false_of_threeNineHyp_A6 h φ

end CFSG.LocalAnalysis.AGL81I.Section3
