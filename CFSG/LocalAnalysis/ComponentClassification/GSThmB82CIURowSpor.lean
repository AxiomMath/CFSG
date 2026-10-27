module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSR

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint
open scoped MatrixGroups

namespace QPUJ6

theorem five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq3 : ¬ (p = 3 ∧ f = 1)) : 5 ≤ p ^ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases Nat.lt_or_ge p 5 with h | h
  · obtain rfl : p = 3 := by
      rcases Nat.lt_or_ge p 4 with h4 | h4
      · omega
      · exfalso
        obtain rfl : p = 4 := by omega
        exact absurd hp (by decide)
    have hf2 : 2 ≤ f := by
      by_contra hf2
      exact hq3 ⟨rfl, by omega⟩
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  · exact h.trans (Nat.le_self_pow (by omega) p)

theorem l4u4_eq_B_of_le
    {M : Type} [Group M] [Finite M] (hZ : IsPGroup 2 (center M)) {s : TauCeti.SporadicName}
    (e : M ⧸ center M ≃* NativeSporadic.Carrier s) (hM : s ≠ .M) {L : Subgroup M} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq3 : ¬ (p = 3 ∧ f = 1))
    (hL : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f) : s = .B ∧ p ^ f = 5 := by
  obtain ⟨A, hcard, -, -, -, hfac⟩ := order_data CatLeafProof.lieOrderFormulasInput hp hp2 hf hL
  have hs := isSimpleGroup hL
  have h5 := five_le_pow hp hp2 hf hq3
  have hp2c : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hpd : p ∣ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
    have h1 : p ∣ (p ^ f) ^ 6 * A :=
      Dvd.dvd.mul_right (dvd_pow (dvd_pow_self p (by omega)) (by norm_num)) _
    rw [← hcard] at h1
    exact hp2c.dvd_of_dvd_mul_right h1
  have hLZ := QPUSpor.inf_center_eq_bot hZ hs hp hp2 hpd
  have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card (M ⧸ center M) :=
    (Subgroup.card_quotient_dvd_card _).trans (QPUSpor.card_dvd_card_quotient_center hLZ)
  rw [Nat.card_congr e.toEquiv, QPUSpor.card_carrier_eq_sporOrder s hM] at h1
  have h2 : (p ^ f) ^ 6 * A ∣ 2 * QPUSpor.sporOrder s := by
    rw [← hcard, mul_comm]
    exact Nat.mul_dvd_mul_left 2 h1
  have h3 : QPUSpor.psp4Num (p ^ f) ∣ 2 * QPUSpor.sporOrder s := by
    refine Dvd.dvd.trans ?_ h2
    rw [QPUSpor.psp4Num, mul_assoc]
    exact Nat.mul_dvd_mul (pow_dvd_pow _ (by norm_num)) hfac
  have h6 : (p ^ f) ^ 6 ∣ 2 * QPUSpor.sporOrder s := (Dvd.intro A rfl).trans h2
  have h4 := QPUSpor.psp4_allowed s hp hp2 hf h5 h3
  cases s <;> simp only [QPUSpor.psp4Allowed, beq_iff_eq, Bool.false_eq_true] at h4
  all_goals first | exact absurd rfl hM | exact ⟨rfl, h4⟩ | skip
  rw [h4] at h6
  exact absurd h6 (by decide)

end QPUJ6

theorem cfQPUJ6Spor_holds :
    CFQPUJ6Spor := by
  intro M _ _ p f hcfg hrep
  obtain ⟨s, ⟨e⟩⟩ := hrep
  obtain ⟨hMq, hZ, hp, hp2, hf, hq3, _E, L, t, J, _J₀, -, -, -, -, hLmod, -, htt, htZ, hJC, hJc,
    hJmod, -⟩ := hcfg
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (M ⧸ center M) := hMq.2.1
  obtain ⟨-, -, -, F, _, _, hF, ⟨eJ⟩⟩ := HarrisLit.exists_psl2_of_lieModel hJmod
  have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := HarrisLit.isSimpleGroup_of_lieModel_psl2 hJmod
  have : IsSimpleGroup (PSL(2, F)) := eJ.symm.isSimpleGroup
  have hna : ∃ a b : PSL(2, F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := HarrisLit.nonabelian_of_lieModel_psl2 hJmod
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  by_cases hsM : s = .M
  · subst hsM
    exact QPUSpor.false_of_components hMq hZ CatalogueU.sporadicOddCoreFree_M e htt htZ hJC hJc
      hna eJ fun u hu B hB => QPUSpor.not_psl2_component_M e hp2 (by omega) hF u hu B hB
  obtain ⟨rfl, hq⟩ := QPUJ6.l4u4_eq_B_of_le hZ e hsM hp hp2 hf hq3 hLmod
  have h7800 : Nat.card (PSL(2, F)) = 7800 := by
    rw [SectionRank.OddCover.card_psl_two hp hp2 hF, pow_mul', hq]
    norm_num
  refine QPUSpor.false_of_components hMq hZ BMCase.sporadicOddCoreFree_B e htt htZ hJC hJc hna
    eJ fun u hu B hB => ⟨fun eB => ?_⟩
  have h17 := (Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
    ⟨e⟩ u hu B hB).2.2
  rw [Nat.card_congr eB.toEquiv, h7800] at h17
  norm_num at h17

end CFSG.ComponentClassification.GSThmB
