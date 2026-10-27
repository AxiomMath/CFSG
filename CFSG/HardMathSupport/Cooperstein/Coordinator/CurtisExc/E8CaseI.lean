module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Orbits

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

theorem two_pow_ge_of_ge_twelve {t : ℕ} (h : 12 ≤ t) : 248 * t + 1 ≤ 2 ^ t := by
  induction t, h using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem five_mul_two_pow_ge {t : ℕ} (h9 : 9 ≤ t) : 248 * t + 1 ≤ 5 * 2 ^ t := by
  rcases Nat.lt_or_ge t 12 with h | h
  · interval_cases t <;> norm_num
  · have := two_pow_ge_of_ge_twelve h
    omega

section CaseI


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

theorem caseI_bound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E8 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E8 K → k} {J : Finset (Fin Tag.E8.rank)}
    (ht : IsChevType .E8 K 2 exists_weyl_neg_E8 ρ y χ J) {s : Fin Tag.E8.rank} (hs7 : s.val ≠ 7)
    (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .E8 K s z) ^ (2 ^ g) = χ (dC .E8 K s z)) :
    248 * (n / g) + 1 ≤ Module.finrank k V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge (n / g) 9 with h8 | h9
  · obtain ⟨w, hw⟩ := exists_orbit_e8Omega_big s hs7
    have := card_le_finrank_of_isChevType hρ ht hs (reflect_e8Omega s) w hw
    omega
  · rcases Nat.lt_or_ge (n / g) 12 with h11 | h12
    · obtain ⟨u, hu1, hu2⟩ := exists_copyWeyl s
      have hli := linearIndependent_translates_of_isChevType hρ ht hs (reflect_e8Omega s) u hu2
      have := copies_finrank hn hK hρ ht hs hg hgn hper u hu1 hli
      have := five_mul_two_pow_ge h9
      omega
    · have := two_pow_le_finrank_of_periodic hn hK hρ ht hs hg hgn hper
      have := two_pow_ge_of_ge_twelve h12
      omega

end CaseI

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
