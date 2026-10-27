module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaMatrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GroupTheory.WeirSylow Module

theorem crossClassical_pomegaOdd : CrossClassical .POmegaOdd 3 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ hn _ h
  have hp := (Fact.out : p.Prime)
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hℓ : ℓ.Prime := hadm.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow (p := ℓ) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hpq : ¬ p ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := F) (n := n)
    (Ring.two_ne_zero h2) hn
  have hdim : finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨r, hOS, hr2⟩ := osylowData_odd (hp.odd_of_ne_two hp2) hpq h2 hn hdim hQnd
  exact WCOn.of_mulEquiv e (wcOn_projOmega_of_sylowData
    (CFSG.LieType.Universal.Spin.coe_quadOdd n F) hQnd hT hp2 hr2 hOS)

theorem crossClassical_pomegaPlus : CrossClassical .POmegaPlus 4 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ hn _ h
  have hp := (Fact.out : p.Prime)
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hℓ : ℓ.Prime := hadm.1
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ p ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := n)
    (by omega)
  have hdim : finrank F (Fin n ⊕ Fin n → F) = 2 * n := finrank_quadPlus_space n
  obtain ⟨r, hOS, hr2⟩ := osylowData_even (hp.odd_of_ne_two hp2) hpq hn hdim hQnd hT
    (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus F n⟩)
  exact WCOn.of_mulEquiv e (wcOn_projOmega_of_sylowData
    (CFSG.LieType.Universal.Spin.coe_quadPlus n F) hQnd hT hp2 hr2 hOS)

theorem crossClassical_pomegaMinus : CrossClassical .POmegaMinus 4 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ hn _ h
  have hp := (Fact.out : p.Prime)
  obtain ⟨hadm, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := h
  have hℓ : ℓ.Prime := hadm.1
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ p ∣ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) hn hirr
  have hdim : finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n :=
    finrank_quadMinus_space (by omega)
  obtain ⟨r, hOS, hr2⟩ := osylowData_even (hp.odd_of_ne_two hp2) hpq hn hdim hQnd hT
    (ε := -1) (Or.inr ⟨rfl, not_isPlusType_quadMinus (by omega) hirr⟩)
  exact WCOn.of_mulEquiv e (wcOn_projOmega_of_sylowData
    (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hQnd hT hp2 hr2 hOS)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
