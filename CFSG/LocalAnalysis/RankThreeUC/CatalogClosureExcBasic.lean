module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.RankThreeUC

theorem charP_two_of_card {K : Type*} [Field K] [Finite K] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) : CharP K 2 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have := Fintype.ofFinite K
  obtain ⟨m, hpp, hm⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card, hm] at hcard
  have hdvd : p ∣ 2 ^ f := by
    rw [← hcard]
    exact dvd_pow_self p m.ne_zero
  have h2 : p ∣ 2 := hpp.dvd_of_dvd_pow hdvd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2
  subst hp2
  exact hp

theorem localRank_le_two_of_no_cube {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (h : ∀ E : Subgroup X, (∀ x ∈ E, x ^ r = 1) → Nat.card E = r ^ 3 → False) :
    CFSG.Assembly.RankThreeEven.localRank r X ≤ 2 := by
  by_contra hlt
  have h3 : 3 ≤ CFSG.Assembly.RankThreeEven.localRank r X := by omega
  obtain ⟨U, -, -, E, -, hE, hcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hr (k := 3) (by norm_num) h3
  exact h E (fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx) hcard

theorem five_le_of_prime_ne {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : 5 ≤ r := by
  have := hr.two_le
  rcases Nat.lt_or_ge r 5 with h5 | h5
  · interval_cases r <;> simp_all (config := {decide := true})
  · exact h5

end CFSG.LocalAnalysis.RankThreeUC
