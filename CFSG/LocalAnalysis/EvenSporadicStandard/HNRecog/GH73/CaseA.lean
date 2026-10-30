module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.CaseAFit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.FrattiniAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.SylowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.YSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.GWApp

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

private lemma prod_fin_three : (∏ i : Fin 3, ((2 : ℕ) ^ 3 - 2 ^ (i : ℕ))) = 168 := by
  decide +kernel

private lemma prod_fin_four : (∏ i : Fin 4, ((2 : ℕ) ^ 4 - 2 ^ (i : ℕ))) = 20160 := by
  decide +kernel

theorem caseA
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hO : CFSG.oddCore X = ⊥) (hE : CFSG.layer X = ⊥) (D : A8SylowData X) :
    Nat.card X = 960 ∨ Nat.card X = 1344 := by
  obtain ⟨j, hj⟩ := D.card_eq
  have hXcard : Nat.card X = 64 * (2 * j + 1) := hj
  have hXnt : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hXcard]
    omega
  haveI := hXnt
  obtain ⟨Q, hQnorm, hQp, hQne, hmax, hcent⟩ := exists_selfCentralizing_two_core hO hE
  haveI : Q.Normal := hQnorm
  have hgen := D.gen_four Q hQp
  obtain ⟨d, hd4, hQbar, hYdvd⟩ := exists_rank_card_dvd Q hQp hgen hmax hcent
  have hQtop : Q ≠ ⊤ := by
    intro htop
    have hpg : IsPGroup 2 X := by
      have hQp' : IsPGroup 2 (⊤ : Subgroup X) := htop ▸ hQp
      exact hQp'.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent X := hpg.isNilpotent
    exact Group.IsPerfect.not_isSolvable X inferInstance
  haveI : Nontrivial (X ⧸ Q) := QuotientGroup.nontrivial_iff.mpr hQtop
  have hY60 : 60 ≤ Nat.card (X ⧸ Q) := perfect_sixty_le_card
  have hY4 : 4 ∣ Nat.card (X ⧸ Q) := perfect_four_dvd_card
  have hXne0 : Nat.card X ≠ 0 := by rw [hXcard]; positivity
  have hQne0 : Nat.card Q ≠ 0 := by
    have h1 : 1 < Nat.card Q := (Subgroup.one_lt_card_iff_ne_bot Q).mpr hQne
    omega
  have hXsplit : Nat.card X = Nat.card (X ⧸ Q) * Nat.card Q :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Q
  have hYne0 : Nat.card (X ⧸ Q) ≠ 0 := by
    intro h
    apply hXne0
    rw [hXsplit, h, zero_mul]
  have hfacX : (Nat.card X).factorization 2 = 6 := by
    rw [hXcard, show (64 : ℕ) = 2 ^ 6 by norm_num]
    rw [Nat.factorization_mul (by positivity) (by omega)]
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_pow_self Nat.prime_two]
    have hz : (2 * j + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat ⟨j, rfl⟩)
    omega
  have hd34 : d = 3 ∨ d = 4 := by
    have hd3 : ¬ d ≤ 2 := by
      intro hd2
      have hprod : (∏ i : Fin d, ((2 : ℕ) ^ d - 2 ^ (i : ℕ))) ≤ 6 := by
        interval_cases d <;> decide +kernel
      have hpos : 0 < (∏ i : Fin d, ((2 : ℕ) ^ d - 2 ^ (i : ℕ))) := by
        interval_cases d <;> decide +kernel
      have hle : Nat.card (X ⧸ Q) ≤ 6 :=
        (Nat.le_of_dvd hpos hYdvd).trans hprod
      omega
    omega
  rcases hd34 with hd3 | hd4
  ·
    subst d
    rw [prod_fin_three] at hYdvd
    have hY168 : Nat.card (X ⧸ Q) = 168 := by
      have h84 : Nat.card (X ⧸ Q) = 84 ∨ Nat.card (X ⧸ Q) = 168 := by
        obtain ⟨m, hm⟩ := hY4
        rw [hm] at hY60 hYdvd ⊢
        have hm42 : m ∣ 42 := by
          rw [show (168 : ℕ) = 4 * 42 by norm_num] at hYdvd
          exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp hYdvd
        have hmge : 15 ≤ m := by omega
        have hmem : m ∈ ({21, 42} : Finset ℕ) := by
          have h1 : m ∈ Nat.divisors 42 := Nat.mem_divisors.mpr ⟨hm42, by norm_num⟩
          have h2 : (Nat.divisors 42).filter (fun x => 15 ≤ x) = ({21, 42} : Finset ℕ) := by
            decide +kernel
          rw [← h2]
          exact Finset.mem_filter.mpr ⟨h1, hmge⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl <;> norm_num
      rcases h84 with h | h
      · exact absurd h (perfect_card_ne_eighty_four (Y := X ⧸ Q))
      · exact h
    obtain ⟨a, ha⟩ := hQp.exists_card_eq
    have hfacQ : (Nat.card Q).factorization 2 = a := by
      rw [ha, Nat.factorization_pow_self Nat.prime_two]
    have hfacY : (Nat.card (X ⧸ Q)).factorization 2 = 3 := by
      rw [hY168, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_pow_self Nat.prime_two]
      have hz : (21 : ℕ).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      omega
    have hmul : (Nat.card (X ⧸ Q)).factorization 2 + (Nat.card Q).factorization 2 = 6 := by
      have h1 : (Nat.card X).factorization 2
          = (Nat.card (X ⧸ Q)).factorization 2 + (Nat.card Q).factorization 2 := by
        rw [hXsplit, Nat.factorization_mul hYne0 hQne0]
        simp
      rw [hfacX] at h1
      exact h1.symm
    have ha3 : a = 3 := by
      rw [hfacQ, hfacY] at hmul
      omega
    have hXfinal : Nat.card X = 1344 := by
      rw [hXsplit, hY168, ha, ha3]
      norm_num
    exact Or.inr hXfinal
  ·
    subst d
    rw [prod_fin_four] at hYdvd
    obtain ⟨a, ha⟩ := hQp.exists_card_eq
    have hfacQ : (Nat.card Q).factorization 2 = a := by
      rw [ha, Nat.factorization_pow_self Nat.prime_two]
    have hmul : (Nat.card (X ⧸ Q)).factorization 2 + (Nat.card Q).factorization 2 = 6 := by
      have h1 : (Nat.card X).factorization 2
          = (Nat.card (X ⧸ Q)).factorization 2 + (Nat.card Q).factorization 2 := by
        rw [hXsplit, Nat.factorization_mul hYne0 hQne0]
        simp
      rw [hfacX] at h1
      exact h1.symm
    have h16dvd : (2 : ℕ) ^ 4 ∣ Nat.card Q := by
      have h := Subgroup.card_quotient_dvd_card (frattini (↥Q))
      rw [hQbar] at h
      simpa using h
    have ha4 : 4 ≤ a := by
      rw [ha] at h16dvd
      have h := (Nat.prime_two.pow_dvd_iff_le_factorization (by positivity)).mp h16dvd
      rwa [Nat.factorization_pow_self Nat.prime_two] at h
    have h2facY : 2 ≤ (Nat.card (X ⧸ Q)).factorization 2 := by
      have h4dvd : (2 : ℕ) ^ 2 ∣ Nat.card (X ⧸ Q) := by simpa using hY4
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hYne0).mp h4dvd
    have haeq : a = 4 := by
      rw [hfacQ] at hmul
      omega
    have hQ16 : Nat.card Q = 16 := by
      rw [ha, haeq]; norm_num
    have hfratt : frattini (↥Q) = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini (↥Q))
      rw [hQbar, hQ16] at hsplit
      have h2 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h2] at hsplit
      omega
    have hcommQ : ∀ x y : ↥Q, x * y = y * x := by
      haveI : IsMulCommutative (↥Q ⧸ frattini (↥Q)) :=
        (CFSG.GroupTheory.frattini_elementary_quotient hQp).2.1
      have hinj : Function.Injective
          (QuotientGroup.mk' (frattini (↥Q)) : ↥Q →* ↥Q ⧸ frattini (↥Q)) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
        exact hfratt
      intro x y
      apply hinj
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
      intro x hx y hy
      simpa using congrArg Subtype.val (hcommQ ⟨x, hx⟩ ⟨y, hy⟩)
    obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
    have hZ := D.card_center S
    have hS := D.card_sylow S
    haveI : IsSimpleGroup (X ⧸ Q) :=
      isSimpleGroup_quotient_of_perfect Q hQab hcent S hQS hZ hS hQ16 hYdvd
    have hnonab : ∃ x y : X ⧸ Q, x * y ≠ y * x := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative (X ⧸ Q) (IsMulCommutative.of_comm h)
    obtain ⟨m, hmeq⟩ := hY4
    have hfacY : (Nat.card (X ⧸ Q)).factorization 2 = 2 := by
      rw [hfacQ] at hmul
      omega
    have hmodd : Odd m := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2m
      obtain ⟨c, hc⟩ := h2m
      have h8 : (2 : ℕ) ^ 3 ∣ Nat.card (X ⧸ Q) := by
        rw [hmeq, hc]
        exact ⟨c, by ring⟩
      have h := (Nat.prime_two.pow_dvd_iff_le_factorization hYne0).mp h8
      omega
    have hY60card : Nat.card (X ⧸ Q) = 60 :=
      simple_card_eq_sixty hnonab hYdvd hmodd hmeq
    have hXfinal : Nat.card X = 960 := by
      calc Nat.card X = Nat.card (X ⧸ Q) * Nat.card Q := hXsplit
        _ = 60 * 16 := by rw [hY60card, hQ16]
        _ = 960 := by norm_num
    exact Or.inl hXfinal

end CFSG.EvenSporadicStandard.HNRecog.GH73
