module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairRegular
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Ω : Type*} [Finite Ω]

theorem regular_elementary_degree_eq_positive_prime_power
    (F : Subgroup (Equiv.Perm Ω)) (p : ℕ) (hp : p.Prime)
    (Q : Subgroup F) [IsElementaryAbelian p Q]
    (hreg : RegularOnEntire F Q) (hdegree : 2 ≤ Nat.card Ω) :
    ∃ n : ℕ, 0 < n ∧ Nat.card Ω = Nat.card Q ∧ Nat.card Ω = p ^ n := by
  have hnonempty : Nonempty Ω :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card Ω by omega)).1
  obtain ⟨a⟩ := hnonempty
  have hcard := regular_card_eq_degree F Q hreg a
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p Q).exists_card_eq
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    rw [hnzero, pow_zero] at hn
    omega
  exact ⟨n, hnpos, hcard.symm, hcard.symm.trans hn⟩

theorem regular_elementary_degree_isPrimePow
    (F : Subgroup (Equiv.Perm Ω)) (p : ℕ) (hp : p.Prime)
    (Q : Subgroup F) [IsElementaryAbelian p Q]
    (hreg : RegularOnEntire F Q) (hdegree : 2 ≤ Nat.card Ω) :
    IsPrimePow (Nat.card Ω) := by
  obtain ⟨n, hn, _, hcard⟩ :=
    regular_elementary_degree_eq_positive_prime_power F p hp Q hreg hdegree
  exact (isPrimePow_nat_iff _).mpr ⟨p, n, hp, hn, hcard.symm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
