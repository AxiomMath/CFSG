module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Copies
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem two_pow_ge_of_ge_five {t : ℕ} (h : 5 ≤ t) : 133 * t + 1 ≤ 21 * 2 ^ t := by
  induction t, h using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

section CaseI


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

theorem caseI_bound_e7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    {s : Fin Tag.E7.rank} (h15 : 1 ≤ s.val ∧ s.val ≤ 5)
    (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .E7 K s z) ^ (2 ^ g) = χ (dC .E7 K s z)) :
    133 * (n / g) + 1 ≤ Module.finrank k V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge (n / g) 5 with h4 | h5
  · obtain ⟨w, hw⟩ := exists_orbit_e7Omega2 s h15
    have := card_le_finrank_of_isChevType hρ ht hs (reflect_e7Omega2 s) w hw
    omega
  · obtain ⟨u, hu1, hu2⟩ := exists_copyWeyl_e7 s h15
    have hli := linearIndependent_translates_of_isChevType hρ ht hs (reflect_e7Omega2 s) u hu2
    have := copies_finrank hn hK hρ ht hs hg hgn hper u hu1 hli
    have := two_pow_ge_of_ge_five h5
    omega

end CaseI

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
