module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringBound
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.FixedTranslate
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Orbit17
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem two_pow_ge_of_ge_twelve {t : ℕ} (h : 12 ≤ t) : 133 * t + 1 ≤ 2 ^ t := by
  induction t, h using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem reflect_v17_of_mem :
    ∀ j : Fin Tag.E7.rank, 1 ≤ j.val → j.val ≤ 5 → reflect .E7 j v17 = v17 := by
  decide +kernel

section CaseII


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

set_option linter.unusedVariables false in
theorem caseII_bound_e7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : ∀ s : Fin Tag.E7.rank, 1 ≤ s.val → s.val ≤ 5 → s ∈ J)
    (h1 : (⟨0, by decide⟩ : Fin Tag.E7.rank) ∉ J) (h7 : (⟨6, by decide⟩ : Fin Tag.E7.rank) ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ (i : Fin Tag.E7.rank) (z : Kˣ), χ (dC .E7 K i z) ^ (2 ^ g) = χ (dC .E7 K i z)) :
    133 * (n / g) + 1 ≤ Module.finrank k V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge (n / g) 12 with h11 | h12
  · obtain ⟨w, hw⟩ := exists_orbit_e7Omega17
    have hfix : ∀ j ∈ J, reflect .E7 j v17 = v17 := by
      intro j hj
      have h0 : j.val ≠ 0 := fun h => h1 (by
        have : j = ⟨0, by decide⟩ := Fin.ext h
        exact this ▸ hj)
      have h6 : j.val ≠ 6 := fun h => h7 (by
        have : j = ⟨6, by decide⟩ := Fin.ext h
        exact this ▸ hj)
      have hlt : j.val < 7 := j.2
      exact reflect_v17_of_mem j (by omega) (by omega)
    have := CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.card_le_finrank_of_isChevType_of_fixed
      hρ ht hfix w hw
    omega
  · have := two_pow_le_finrank_of_periodic hn hK hρ ht h7 hg hgn (hper ⟨6, by decide⟩)
    have := two_pow_ge_of_ge_twelve h12
    omega

end CaseII

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
