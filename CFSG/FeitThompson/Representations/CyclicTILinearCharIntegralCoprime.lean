module

public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues
public import CFSG.FeitThompson.Representations.CoprimePowerPermutesIrreducibles
public import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.CharacterConstantOnCyclicGeneratorsInteger
import CFSG.FeitThompson.Representations.CyclicTIIsometryPowerEquivariance
import CFSG.FeitThompson.Representations.CentralScalarInductionDegreeSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem exists_one_le_coprime_modEq_modEq_one {N m M a : ℕ} (hN : N ≠ 0) (hm : m ≠ 0)
    (hM : M ≠ 0) (hNm : N.Coprime m) (ha : a.Coprime N) :
    ∃ k : ℕ, 1 ≤ k ∧ k.Coprime M ∧ k ≡ a [MOD N] ∧ k ≡ 1 [MOD m] := by
  classical
  set S : Finset ℕ := {p ∈ M.primeFactors | ¬ p ∣ N ∧ ¬ p ∣ m} with hS
  set R : ℕ := ∏ p ∈ S, p with hRdef
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos.ne'
  have hRN : R.Coprime N := Nat.Coprime.prod_left fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).coprime_iff_not_dvd.2
      (Finset.mem_filter.1 hp).2.1
  have hNmR : N.Coprime (m * R) := Nat.Coprime.mul_right hNm hRN.symm
  obtain ⟨k₀, h1, h2⟩ := Nat.chineseRemainder hNmR a 1
  have hc : 0 < N * (m * R) := Nat.pos_of_ne_zero (by simp [hN, hm, hR0])
  have hmodN : k₀ + N * (m * R) ≡ a [MOD N] := by
    have h : k₀ + N * (m * R) ≡ k₀ + 0 [MOD N] :=
      Nat.ModEq.add_left k₀ ((Nat.modEq_zero_iff_dvd).2 (Dvd.intro _ rfl))
    simpa using h.trans h1
  have hmodmR : k₀ + N * (m * R) ≡ 1 [MOD m * R] := by
    have h : k₀ + N * (m * R) ≡ k₀ + 0 [MOD m * R] :=
      Nat.ModEq.add_left k₀ ((Nat.modEq_zero_iff_dvd).2 (Dvd.intro_left _ rfl))
    simpa using h.trans h2
  refine ⟨k₀ + N * (m * R), by omega, ?_, hmodN, hmodmR.of_dvd (Dvd.intro R rfl)⟩
  refine Nat.coprime_of_dvd fun p hp hpk hpM => ?_
  have hpk0 : k₀ + N * (m * R) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hpk
  have key : p ∣ N ∨ p ∣ m * R := by
    by_cases hpN : p ∣ N
    · exact Or.inl hpN
    by_cases hpm : p ∣ m
    · exact Or.inr (hpm.mul_right R)
    refine Or.inr (Dvd.dvd.mul_left ?_ m)
    exact Finset.dvd_prod_of_mem id (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpM, hM⟩,
      hpN, hpm⟩)
  rcases key with hpN | hpmR
  · have h4 : (0 : ℕ) ≡ a [MOD p] := (hpk0.symm).trans (hmodN.of_dvd hpN)
    have hpa : p ∣ a := (Nat.modEq_zero_iff_dvd).1 h4.symm
    exact hp.one_lt.ne' (Nat.dvd_one.1 (ha ▸ Nat.dvd_gcd hpa hpN))
  · have h4 : (0 : ℕ) ≡ 1 [MOD p] := (hpk0.symm).trans (hmodmR.of_dvd hpmR)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 h4.symm))

def linearCharClassFun {X : Type*} [Group X] (w : X →* ℂˣ) : classFun X :=
  ⟨fun x => (w x : ℂ), Irr_subset_classFun (monoidHom_mem_Irr ((Units.coeHom ℂ).comp w))⟩

@[simp]
theorem coe_linearCharClassFun {X : Type*} [Group X] (w : X →* ℂˣ) :
    (linearCharClassFun w : X → ℂ) = fun x => (w x : ℂ) := (rfl)

@[simp]
theorem linearCharClassFun_apply {X : Type*} [Group X] (w : X →* ℂˣ) (x : X) :
    (linearCharClassFun w : X → ℂ) x = (w x : ℂ) := (rfl)

theorem linearCharClassFun_mem_Irr {X : Type*} [Group X] (w : X →* ℂˣ) :
    (linearCharClassFun w : X → ℂ) ∈ Irr X :=
  monoidHom_mem_Irr ((Units.coeHom ℂ).comp w)

theorem linearCharClassFun_mem_virtualChars {X : Type*} [Group X] (w : X →* ℂˣ) :
    (linearCharClassFun w : X → ℂ) ∈ virtualChars X :=
  mem_virtualChars_of_mem_span_Irr (Submodule.subset_span (linearCharClassFun_mem_Irr w))

theorem coe_linearCharClassFun_eq_linearCharFun {A : Type*} [CommGroup A] (w : A →* ℂˣ) :
    (linearCharClassFun w : A → ℂ) = linearCharFun w :=
  funext fun x => (linearCharFun_apply w x).symm

theorem powOpₗ_linearCharClassFun {X : Type*} [Group X] {w : X →* ℂˣ} {m k : ℕ}
    (hw : ∀ x : X, w x ^ m = 1) (hk : k ≡ 1 [MOD m]) (hk1 : 1 ≤ k) :
    classFun.powOpₗ X k (linearCharClassFun w) = linearCharClassFun w := by
  obtain ⟨t, ht⟩ : m ∣ k - 1 := (Nat.modEq_iff_dvd' hk1).1 hk.symm
  refine Subtype.ext (funext fun x => ?_)
  rw [classFun.coe_powOpₗ_apply, coe_linearCharClassFun, powOp_apply]
  have hkk : k = 1 + m * t := by omega
  rw [hkk, map_pow, pow_add, pow_one, pow_mul, hw x, one_pow, mul_one]

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype W]
  {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem exists_int_apply_linearCharClassFun (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (w : ↥W →* ℂˣ) {m : ℕ} (hm1 : 1 ≤ m)
    (hw : ∀ x : ↥W, w x ^ m = 1) {g : G} (hgm : (orderOf g).Coprime m) :
    ∃ n : ℤ, (σ (linearCharClassFun w) : G → ℂ) g = n := by
  have hspan : (σ (linearCharClassFun w) : G → ℂ) ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars
      (hσ.map_virtualChars _ (linearCharClassFun_mem_virtualChars w))
  refine exists_int_apply_of_apply_pow_eq hspan g fun a ha => ?_
  obtain ⟨ha1, haN, haco⟩ := mem_coprimeIndices.1 ha
  obtain ⟨k, hk1, hkG, hkN, hkm⟩ := exists_one_le_coprime_modEq_modEq_one
    (isOfFinOrder_of_finite g).orderOf_pos.ne' (by omega) (Nat.card_pos (α := G)).ne' hgm haco
  have hga : g ^ k = g ^ a := pow_eq_pow_iff_modEq.2 hkN
  have hkey := hσ.apply_powOpₗ_apply hW hk1 hkG (linearCharClassFun w) g
  rw [powOpₗ_linearCharClassFun hw hkm hk1] at hkey
  rw [← hga]
  exact hkey.symm

end CFSG.FeitThompson
