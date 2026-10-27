module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUChar
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.Coordinator CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.Classical

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_ne_one_mem_primeFormD (h : UnitaryFieldData ℓ f K) (hq : ¬(3 = 3 ∧ ℓ ^ f = 2))
    {D : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) :
    ∃ x ∈ D, x ≠ 1 ∧ x ∈ primeFormD h (idGram K 3) := by
  classical
  have := h.finite
  have hDfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  set φ : D →* (K ≃+* K) := (primeFormFieldFactor h hC le_rfl hq).comp D.subtype with hφ
  have hle := card_le_mul_card_ker' Nat.prime_three (fun x : D => Subtype.ext (hD.2 x x.2)) φ
  have hk : 1 < Nat.card φ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card D ≤ 3 * 1 := hle.trans (Nat.mul_le_mul_left _ hlt)
    rw [hcard] at this
    omega
  obtain ⟨⟨x, hxk⟩, hx1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).1 hk |> Subgroup.ne_bot_iff_exists_ne_one.1
  refine ⟨x.1, x.2, fun h1 => hx1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rw [← ker_primeFormFieldFactor h hC le_rfl hq]
  exact hxk

theorem primeFormConj_eq_one_of_mem_localDeltaIn
    (h : UnitaryFieldData ℓ f K) (hq : 2 < ℓ ^ f)
    {D : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    {H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) (Y : primeFormUnitary h (idGram K 3))
    (hY : primeFormConjHom h (idGram K 3) Y ∈ localDeltaIn 3 H D) :
    primeFormConjHom h (idGram K 3) Y = 1 := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := by omega
  have := h.finite
  have hℓ := h.prime
  by_cases hl3 : ℓ = 3
  ·
    subst hl3
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
    have := le_core_of_mem_localDeltaIn hY hxD hx1
    rw [h0] at this
    exact Subgroup.mem_bot.1 this
  · by_cases hDl : D ≤ primeFormD h (idGram K 3)
    · by_cases hpq : 3 ∣ ℓ ^ f + 1
      · have hq3 : 3 < ℓ ^ f := by
          by_contra hle
          have h3 : ℓ ^ f = 3 := by omega
          rw [h3] at hpq
          omega
        exact primeFormConj_eq_one_of_pgu_plane h hq3 hpq hD hcard hDl hH Y hY
      · have hpg : ¬ (3 : ℕ) ∣ Nat.gcd 3 (ℓ ^ f + 1) := fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
        have hEinn : D ≤ (MulAut.conj : primeFormP h (idGram K 3) →*
            MulAut (primeFormP h (idGram K 3))).range := fun x hx =>
          mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin 3) K) hp hpg (hDl hx) (hD.2 x hx)
        have hDel : CFSG.IsElementaryAbelian 3 ↥D :=
          { toIsMulCommutative := hD.1
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext (hD.2 x x.2) }
        have h0 := localDeltaIn_eq_bot_primeFormP h hn hne hp hp2 (Ne.symm hl3) hpg
          (by omega) D hEinn hDel hcard hH
        rw [h0] at hY
        exact Subgroup.mem_bot.1 hY
    · by_cases hq0 : ℓ ^ (f / 3) = 2
      · have hℓ2 : ℓ = 2 := by
          have := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq0
          exact this.1
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
        exact eq_one_of_q8_of_mem h hσ hH hxD hM hY
      · have h0 := localDeltaIn_eq_bot_of_not_le_primeFormD_three h hne (by omega) hD hDl hH
        rw [h0] at hY
        exact Subgroup.mem_bot.1 hY


theorem psuConj_eq_one_of_mem_localDeltaIn {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {D H : Subgroup (MulAut (unitaryPSU h 3))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 9) (hH : innerAut (unitaryPSU h 3) ≤ H) {A : unitaryIsom3 h}
    (hα : psuConj h A ∈ localDeltaIn 3 H D) : psuConj h A = 1 :=
  psuConj_eq_one_of_primeForm h
    (fun hD' hcard' hH' Y hY => primeFormConj_eq_one_of_mem_localDeltaIn h hq hD' hcard' hH' Y hY)
    hD hcard hH hα

end CFSG.HardMathSupport.Solomon.Coordinator
