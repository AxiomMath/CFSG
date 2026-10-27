module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem five_le_of_prime_of_ne {d : ℕ} (hd : d.Prime) (h2 : d ≠ 2) (h3 : d ≠ 3) : 5 ≤ d := by
  have h2le := hd.two_le
  by_contra hlt
  interval_cases d
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hd (by decide)

theorem false_of_threeNineHyp_A6 (h : ThreeNineHyp K E D X₁ 3 d)
    (φ : ↥K ≃* alternatingGroup (Fin 6)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hA := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
    rw [eq_bot_iff]
    intro z hz
    have : φ z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro a
      obtain ⟨b, rfl⟩ := φ.surjective a
      rw [← map_mul, ← map_mul, hz b]
    rw [hA, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact φ.injective (by rw [this, map_one])
  have hOut : Nat.card (Outer ↥K) = Nat.card (Outer (alternatingGroup (Fin 6))) :=
    CFSG.Sporadic.SteinbergBI.card_outer_eq_of_mulEquiv φ
  have hout3 : ¬ 3 ∣ Nat.card (Outer ↥K) := by
    rw [hOut]
    exact CFSG.RankThree.PartTwo.Sec4.Item434Alt.not_three_dvd_card_outer_six
  have hle : Nat.card (Outer ↥K) ≤ 4 := by
    rw [hOut]
    exact CFSG.RankThree.PartOne.card_outer_alternating_le_four (by norm_num)
  have hpos : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hd5le : 5 ≤ d := five_le_of_prime_of_ne h.d_prime h.d_ne_two h.d_ne
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    have := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨hY, hm3, hmd, h3Y, hdY, hdK⟩ := h.index_facts hZ hout3 houtd
  rw [hcard] at h3Y hdY hdK
  have hd5 : d = 5 := by
    have hfac : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp h1
  subst hd5
  have h9 : (3 : ℕ) ^ (360 : ℕ).factorization 3 = 9 := by
    have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 2)
      (k := 40) (N := 360) (by norm_num) (by norm_num)).symm
    rw [this]
    norm_num
  have h5 : (5 : ℕ) ^ (360 : ℕ).factorization 5 = 5 := by
    have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 5) (a := 1)
      (k := 72) (N := 360) (by norm_num) (by norm_num)).symm
    rw [this]
    norm_num
  rw [h9] at h3Y
  rw [h5] at hdY
  have h45 : 45 ∣ Nat.card (X₁.subgroupOf K) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 5) h3Y hdY
  have hidx := index_dvd_div_of_dvd_card h45
  rw [hcard] at hidx
  have key : ∀ m ∈ Nat.divisors 8, m ≡ 1 [MOD 3] → m ≡ 1 [MOD 5] → m = 1 := by decide
  have h1 := key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hm3 hmd
  exact hY (Subgroup.index_eq_one.mp h1)

end CFSG.LocalAnalysis.AGL81I.Section3
