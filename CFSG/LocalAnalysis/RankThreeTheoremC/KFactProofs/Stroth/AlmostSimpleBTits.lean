module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerReduce
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Res417Seven
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem eq_three_or_five_of_sq_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 17971200) : p = 3 ∨ p = 5 := by
  have h1 : p ∣ 17971200 := (dvd_pow_self p two_ne_zero).trans h
  have hfac : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
  rw [hfac] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)) hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h1))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h1))
  · have hp13 : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1
    subst hp13
    exact absurd h (by norm_num)

theorem isRankTwoSEGroup_five_of_tits {L : Type} [Group L] (h : IsoLie L .tits) :
    IsRankTwoSEGroup 5 L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl h⟩))))

section Three


theorem pClosureOdd_three_titsD : PClosureOdd 3 ↥titsD := by
  intro x hx1 hx3
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨P, hP3, -, hPy⟩ := exists_pGroup_of_titsD hx
  intro K _ hKle hcop
  have hle : pElemClosure 3 ↥(Subgroup.centralizer ({x} : Set ↥titsD)) ≤
      P.comap (Subgroup.centralizer ({x} : Set ↥titsD)).subtype := by
    rw [pElemClosure, Subgroup.closure_le]
    rintro y ⟨j, hj⟩
    have hy3 : (y : ↥titsD) ^ 3 = 1 :=
      pow_three_eq_one_of_titsD ⟨j, by simpa using congrArg Subtype.val hj⟩
    exact hPy (y : ↥titsD) y.2 hy3
  have hbot : K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hkP : (k : ↥titsD) ∈ P := hle (hKle hk)
    obtain ⟨j, hj⟩ := hP3 ⟨(k : ↥titsD), hkP⟩
    have hj' : k ^ 3 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    have h1 : orderOf k ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have h2 : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hk
    have hc : Nat.Coprime (3 ^ j) (Nat.card K) := Nat.Coprime.pow_left j hcop
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  subst hbot
  simp

end Three

section Main


theorem chevTwoPClosureOddTits_holds : ChevTwoPClosureOddFamily LieFamilyTits := by
  intro p hp hp2 L _ _ _ _ hrk hSE ⟨dd, hv⟩ hF _ he
  cases dd with
  | tits =>
    obtain ⟨e⟩ := he
    have hiso : IsoLie L .tits := ⟨hv, ⟨e⟩⟩
    obtain ⟨eS⟩ := titsModelEquiv L 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hiso)
    obtain ⟨E, -, hEcard⟩ := exists_isElemAbelian_card_sq_of_pRank_eq_two hp hrk
    have hdvd : p ^ 2 ∣ 17971200 := by
      rw [← card_titsD, ← Nat.card_congr eS.toEquiv, ← hEcard]
      exact Subgroup.card_subgroup_dvd_card E
    rcases eq_three_or_five_of_sq_dvd hp hp2 hdvd with rfl | rfl
    · exact PClosureOdd.of_mulEquiv eS.symm pClosureOdd_three_titsD
    · exact absurd (isRankTwoSEGroup_five_of_tits hiso) hSE
  | _ => exact absurd hF (by simp [LieFamilyTits])

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
