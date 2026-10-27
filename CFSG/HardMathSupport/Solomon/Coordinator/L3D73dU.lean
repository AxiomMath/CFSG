module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUMain
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8Gen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.Coordinator CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem localDeltaIn_eq_bot_of_not_le_primeFormD_all (h : UnitaryFieldData ℓ f K)
    (hq : 2 < ℓ ^ f) {D : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hDl : ¬ D ≤ primeFormD h (idGram K 3)) {H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) : localDeltaIn 3 H D = ⊥ := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  have := h.finite
  have hℓ := h.prime
  by_cases hl3 : ℓ = 3
  · subst hl3
    have hpg : ¬ (3 : ℕ) ∣ Nat.gcd 3 (3 ^ f + 1) := by
      intro hd
      have h1 : 3 ∣ 3 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
      have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
      omega
    obtain ⟨x, hxD, hx1, hxl⟩ := exists_ne_one_mem_primeFormD h hne hD hcard
    have hxo : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
    have hxi : x ∈ innerAut (primeFormP h (idGram K 3)) :=
      mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin 3) K) hp hpg hxl (hD.2 x hxD)
    have h0 := gLAPPrimeCoreOf_eq_bot_primeFormP_char h le_rfl (by omega) hp2 hxi hxo hH
    rw [eq_bot_iff]
    intro g hg
    have := le_core_of_mem_localDeltaIn hg hxD hx1
    rw [h0] at this
    exact this
  · by_cases hq0 : ℓ ^ (f / 3) = 2
    · have hℓ2 : ℓ = 2 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0).1
      subst hℓ2
      have hf1 : f / 3 = 1 := ((Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0).2
      have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
      obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
      have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
      have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
      have hσ1 : primeFormFieldFactor h hC hn hne x ≠ 1 := fun h1 => hxl (by
        rw [← ker_primeFormFieldFactor h hC hn hne]
        exact h1)
      have hσ : orderOf (primeFormFieldFactor h hC hn hne x) = 3 :=
        orderOf_eq_prime (by rw [← map_pow, hD.2 x hxD, map_one]) hσ1
      obtain ⟨-, -, -, -, -, M, hM⟩ :=
        unitary_prime_semilinear_field_descent' h hn hne hp hp2 x hxp _ rfl hσ
      have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσ).1
      have hf3 : f = 3 := by omega
      subst hf3
      exact localDeltaIn_eq_bot_of_q8_of_mem h hσ hH hxD hM
    · exact localDeltaIn_eq_bot_of_not_le_primeFormD_three h hne (by omega) hD hDl hH

theorem localDeltaIn_eq_bot_of_not_le_psuConj {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {D H : Subgroup (MulAut (unitaryPSU h 3))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 9) (hDl : ¬ D ≤ (psuConj h).range)
    (hH : innerAut (unitaryPSU h 3) ≤ H) : localDeltaIn 3 H D = ⊥ := by
  set φ : MulAut (unitaryPSU h 3) ≃* MulAut (primeFormP h (idGram K 3)) :=
    MulAut.congr (psuToPrimeForm h) with hφ
  have hcard9 : Nat.card D = 3 ^ 2 := by rw [hcard]; norm_num
  have hD' : IsElemAbelian 3 (D.map φ.toMonoidHom) :=
    (isEkIn_map_mulEquiv 3 2 φ (A := ⊤) (D := D) ⟨le_top, hD, hcard9⟩).2.1
  have hcard' : Nat.card (D.map φ.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hcard9]
  have hH' : innerAut (primeFormP h (idGram K 3)) ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj ((psuToPrimeForm h).symm x), hH ⟨_, rfl⟩, ?_⟩
    change MulAut.congr (psuToPrimeForm h) (MulAut.conj ((psuToPrimeForm h).symm x)) =
      MulAut.conj x
    rw [congr_conj_apply, MulEquiv.apply_symm_apply]
  have hDl' : ¬ D.map φ.toMonoidHom ≤ primeFormD h (idGram K 3) := by
    intro hle
    apply hDl
    intro x hx
    obtain ⟨Y, hY⟩ := hle ⟨x, hx, rfl⟩
    have hYmem : (Y : GL (Fin 3) K) ∈ unitaryIsom3 h := by
      have := Y.2
      change (((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) at this
      rw [Units.val_one, Matrix.mul_one] at this
      exact this
    exact ⟨⟨Y, hYmem⟩, φ.injective ((congr_psuConj h ⟨Y, hYmem⟩).trans hY)⟩
  have h0 := localDeltaIn_eq_bot_of_not_le_primeFormD_all h hq hD' hcard' hDl' hH'
  rw [localDeltaIn_map_mulEquiv] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h0

end CFSG.HardMathSupport.Solomon.Coordinator
