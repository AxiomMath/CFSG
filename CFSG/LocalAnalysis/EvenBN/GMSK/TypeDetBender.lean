module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf

namespace TypeDet

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · exact Dvd.dvd.mul_left
      ((show 3 ∣ q - 1 by omega).trans (CatLeafProof.sub_one_dvd_sq_sub_one q)) _
  · exact Dvd.dvd.mul_left
      ((show 3 ∣ q + 1 by omega).trans (CatLeafProof.add_one_dvd_sq_sub_one q)) _

theorem three_mul_dvd_pow_mul {q N C b d : ℕ} (hN : N ≠ 0) (hC : (q ^ 2 - 1) * b ∣ C)
    (hd : d ∣ b) : 3 * d ∣ q ^ N * C :=
  calc 3 * d ∣ q * (q ^ 2 - 1) * b := mul_dvd_mul (three_dvd_mul_sq_sub_one q) hd
    _ = q * ((q ^ 2 - 1) * b) := mul_assoc _ _ _
    _ ∣ q ^ N * C := mul_dvd_mul (dvd_pow_self q hN) hC

theorem sq_sub_one_dvd_pow_four_sub_one (q : ℕ) : q ^ 2 - 1 ∣ q ^ 4 - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 2
  rwa [← pow_mul, one_pow] at this

theorem tri_ne_zero {n : ℕ} (hn : 2 ≤ n) : n * (n - 1) / 2 ≠ 0 := by
  have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  omega

theorem three_mul_lieOrderDivisor_dvd {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (ht : t ≠ .twistedB2) :
    3 * lieOrderDivisor t n (p ^ f) ∣ lieOrderNumerator t n (p ^ f) := by
  rw [CatLeafProof.lieOrderNumerator_eq hadm]
  have hp := hadm.1
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  set q := p ^ f with hq
  have hsub : ∀ i, q - 1 ∣ q ^ i - 1 := fun i => by
    simpa using Nat.sub_dvd_pow_sub_pow q 1 i
  have hadd : ∀ i, Odd i → q + 1 ∣ q ^ i + 1 := fun i hi => by
    simpa using hi.nat_add_dvd_pow_add_pow q 1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · rw [Finset.Icc_self, Finset.prod_singleton, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num))
        (three_dvd_mul_sq_sub_one q) ((Nat.gcd_dvd_right _ _).trans ((hsub 2).mul_left _))
    · have hs : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Icc]
        omega
      have hC : (q ^ 2 - 1) * (q ^ 3 - 1) ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
        have := Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hs
        rwa [Finset.prod_pair (by norm_num)] at this
      exact three_mul_dvd_pow_mul (tri_ne_zero (by omega)) hC
        ((Nat.gcd_dvd_right _ _).trans (hsub 3))
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have hs : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have hC : (q ^ 2 - 1) * (q ^ 3 + 1) ∣
        ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _
        (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hs
      rw [Finset.prod_pair (by norm_num)] at this
      simpa only [even_two, ite_true, show ¬ Even 3 by decide, ite_false] using this
    exact three_mul_dvd_pow_mul (tri_ne_zero (by omega)) hC
      ((Nat.gcd_dvd_right _ _).trans (hadd 3 (by decide)))
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have hs : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have hC : (q ^ 2 - 1) * (q ^ 4 - 1) ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ (2 * i) - 1) hs
      rwa [Finset.prod_pair (by norm_num)] at this
    exact three_mul_dvd_pow_mul (pow_ne_zero 2 (by omega)) hC
      ((Nat.gcd_dvd_right _ _).trans (hsub 4))
  case POmegaOdd =>
    obtain ⟨-, -, hn, hp2⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have hs : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have hC : (q ^ 2 - 1) * (q ^ 4 - 1) ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ (2 * i) - 1) hs
      rwa [Finset.prod_pair (by norm_num)] at this
    have hodd : Odd q := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have h2 : 2 ∣ q - 1 := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩
    exact three_mul_dvd_pow_mul (pow_ne_zero 2 (by omega)) hC (h2.trans (hsub 4))
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hP : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1
    exact three_mul_dvd_pow_mul (Nat.mul_ne_zero (by omega) (by omega))
      ((dvd_of_eq (mul_comm _ _)).trans (mul_dvd_mul_left _ hP)) (Nat.gcd_dvd_right _ _)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hP : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1
    exact three_mul_dvd_pow_mul (Nat.mul_ne_zero (by omega) (by omega))
      ((dvd_of_eq (mul_comm _ _)).trans (mul_dvd_mul_left _ hP)) (Nat.gcd_dvd_right _ _)
  case G2 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := 1) (by norm_num) ⟨q ^ 6 - 1, by ring⟩ (one_dvd _)
  case F4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := 1) (by norm_num)
      ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1), by ring⟩ (one_dvd _)
  case E6 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := q ^ 9 - 1) (by norm_num)
      ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hsub 9))
  case E7 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := q ^ 18 - 1) (by norm_num)
      ⟨(q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hsub 18))
  case E8 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := 1) (by norm_num)
      ⟨(q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1), by ring⟩ (one_dvd _)
  case twistedE6 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := q ^ 9 + 1) (by norm_num)
      ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hadd 9 (by decide)))
  case trialityD4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact three_mul_dvd_pow_mul (b := 1) (by norm_num)
      ⟨(q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1), by ring⟩ (one_dvd _)
  case twistedB2 => exact absurd rfl ht
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor, mul_one]
    have h3q : 3 ∣ q := by
      rw [hq, hp3]
      exact dvd_pow_self 3 hf
    exact Dvd.dvd.mul_right (dvd_pow h3q (by norm_num)) _
  case twistedF4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h4 := sq_sub_one_dvd_pow_four_sub_one q
    refine three_mul_dvd_pow_mul (b := 1) (by norm_num) ?_ (one_dvd _)
    rw [mul_one]
    exact ((h4.mul_left _).mul_right _).mul_right _
  case Tits =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor, mul_one]
    exact Dvd.dvd.mul_left (by norm_num) _

theorem two_pow_mod_three_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_ordSuzuki {q : ℕ} (hq : q % 3 = 2) : ¬ 3 ∣ ordSuzuki q := by
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · omega
    · omega
  · omega

theorem evenLieOrder_eq_ordTwistedA_two {t : StatedLieTag} {n g f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hf : 2 ≤ f)
    (h : SeitzReduction.F4Pilot.evenLieOrder t n g = ordTwistedA 2 (2 ^ f)) :
    t = .PSU ∧ n = 3 ∧ g = f := by
  have h' : RankThree.PartOne.S12K.charTwoOrder t n g = ordTwistedA 2 (2 ^ f) := by
    cases t
    case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
    all_goals exact h
  exact RankThree.PartOne.S12K.rigid_U hadm hf h'

theorem two_le_of_lieModel_PSU_three_two {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSU 3 2 f) : 2 ≤ f := by
  obtain ⟨-, hf, -, h32⟩ := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h
  by_contra hlt
  obtain rfl : f = 1 := by omega
  exact h32 rfl

end TypeDet

open TypeDet

theorem not_three_dvd_card_twistedB2_of_lieModel {X : Type}
    [Group X] {n p f : ℕ} (h : LieModel X .twistedB2 n p f) : ¬ 3 ∣ Nat.card X := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact absurd hrt (by decide)
  · obtain ⟨-, a, -, rfl, hc⟩ := GH74.card_of_suzukiModel hsz
    rw [hc]
    exact not_three_dvd_ordSuzuki (two_pow_mod_three_of_odd ⟨a, rfl⟩)

section Orders


theorem three_dvd_card_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (h : LieModel X t n p f) (ht : t ≠ .twistedB2) :
    3 ∣ Nat.card X := by
  obtain ⟨-, hmul, -⟩ := CatLeafProof.lieOrderFormulasInput X t n p f hadm h
  have h3 := three_mul_lieOrderDivisor_dvd hadm ht
  rw [← hmul] at h3
  exact Nat.dvd_of_mul_dvd_mul_right
    (Nat.pos_of_ne_zero (CatLeafProof.lieOrderDivisor_ne_zero hadm)) h3

theorem su3EvenTypeDet : SeitzReduction.UnitaryPilot.SUmEvenTypeDetAt 3 := by
  intro X _ f t n f' hX _ h
  have he := SeitzReduction.F4Pilot.card_eq_evenLieOrder h
  rw [SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hX] at he
  exact evenLieOrder_eq_ordTwistedA_two
    (SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h)
    (two_le_of_lieModel_PSU_three_two hX) he.symm

theorem szEvenTypeDet :
    ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
      LieModel X .twistedB2 0 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
        t = .twistedB2 ∧ n = 0 ∧ f' = f := by
  intro X _ f t n f' hX hadm h
  by_cases ht : t = .twistedB2
  · subst ht
    obtain ⟨-, -, rfl, -, -, -⟩ := hadm
    refine ⟨rfl, rfl, ?_⟩
    have h1 := (CatLeafProof.lieOrderFormulasInput X .twistedB2 0 2 f
      (SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX) hX).2.2
    have h2 := (CatLeafProof.lieOrderFormulasInput X .twistedB2 0 2 f'
      (SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h) h).2.2
    simp only [lieSylowExponent] at h1 h2
    omega
  · exact absurd (three_dvd_card_of_lieModel hadm h ht)
      (not_three_dvd_card_twistedB2_of_lieModel hX)

theorem szNotOddLie {X : Type} [Group X] {n p f : ℕ} (h : LieModel X .twistedB2 n p f) :
    ¬ OddLieType X := by
  rintro ⟨t, n', p', f', -, hp2, hadm, hX⟩
  by_cases ht : t = .twistedB2
  · subst ht
    exact hp2 hadm.2.2.2.1
  · exact not_three_dvd_card_twistedB2_of_lieModel h (three_dvd_card_of_lieModel hadm hX ht)

theorem szNotOddLie_of_suzukiModel {X : Type} [Group X] {p f : ℕ} (h : SuzukiModel X p f) :
    ¬ OddLieType X :=
  szNotOddLie (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))

end Orders

end CFSG.LocalAnalysis.EvenBN.GMSK
