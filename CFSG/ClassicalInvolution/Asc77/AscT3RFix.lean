module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10C
public import CFSG.ClassicalInvolution.Asc77.AscT3CII9Eps
public import CFSG.ClassicalInvolution.AschTight.Lemma33

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Fix

variable {F : Type} [Field F]

@[expose] def fixSub (i : MulAut SL(2, F)) : Subgroup SL(2, F) :=
  MonoidHom.eqLocus (i : SL(2, F) →* SL(2, F)) (MonoidHom.id _)

theorem mem_fixSub {i : MulAut SL(2, F)} {x : SL(2, F)} : x ∈ fixSub i ↔ i x = x := Iff.rfl

theorem fixSub_conj (γ i : MulAut SL(2, F)) :
    fixSub (γ * i * γ⁻¹) = (fixSub i).map (γ : SL(2, F) →* SL(2, F)) := by
  ext x
  constructor
  · intro hx
    refine ⟨γ⁻¹ x, ?_, by simp⟩
    have h : γ (i (γ⁻¹ x)) = x := hx
    show i (γ⁻¹ x) = γ⁻¹ x
    apply γ.injective
    rw [h]
    simp
  · rintro ⟨y, hy, rfl⟩
    show γ (i (γ⁻¹ (γ y))) = γ y
    rw [MulAut.inv_apply_self]
    have : i y = y := hy
    rw [this]

end Fix

section Sub

variable {F : Type} [Field F]

abbrev fixField (σ : F ≃+* F) : Subfield F := FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixField {σ : F ≃+* F} {x : F} : x ∈ fixField σ ↔ σ x = x := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h m
    obtain ⟨m, hm⟩ := m
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    have h2 : σ⁻¹ x = x := by
      calc σ⁻¹ x = σ.symm x := rfl
        _ = σ.symm (σ x) := by rw [h]
        _ = x := σ.symm_apply_apply x
    have key : ∀ k : ℤ, (σ ^ k) x = x := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ k ih =>
        rw [zpow_add_one]
        change (σ ^ (k : ℤ)) (σ x) = x
        rw [h]
        exact ih
      | pred k ih =>
        rw [zpow_sub_one]
        change (σ ^ (-(k : ℤ))) (σ⁻¹ x) = x
        rw [h2]
        exact ih
    exact key k

@[expose] noncomputable def thetaF (σ : F ≃+* F) : SL(2, fixField σ) →* SL(2, F) :=
  Matrix.SpecialLinearGroup.map (fixField σ).subtype

theorem thetaF_entry (σ : F ≃+* F) (A : SL(2, fixField σ)) (i j : Fin 2) :
    ((thetaF σ A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      (((A : Matrix (Fin 2) (Fin 2) (fixField σ)) i j : fixField σ) : F) :=
  rfl

theorem thetaF_injective (σ : F ≃+* F) : Function.Injective (thetaF σ) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h1 := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) i j) h
  exact Subtype.ext h1

theorem range_thetaF (σ : F ≃+* F) : (thetaF σ).range = fixSub (slFieldAut F σ) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    show slFieldAut F σ (thetaF σ A) = thetaF σ A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [slFieldAut_entry, thetaF_entry]
    exact mem_fixField.mp (A i j).2
  · intro hx
    have hx' : slFieldAut F σ x = x := hx
    have hent : ∀ i j,
        σ ((x : Matrix (Fin 2) (Fin 2) F) i j) = (x : Matrix (Fin 2) (Fin 2) F) i j :=
      fun i j => by
        have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) i j) hx'
        simpa [slFieldAut_entry] using this
    let B : Matrix (Fin 2) (Fin 2) (fixField σ) :=
      fun i j => ⟨(x : Matrix (Fin 2) (Fin 2) F) i j, mem_fixField.mpr (hent i j)⟩
    have hdet : B.det = 1 := by
      apply Subtype.ext
      have h1 := x.2
      rw [Matrix.det_fin_two] at h1 ⊢
      simpa [B] using h1
    refine ⟨⟨B, hdet⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl

end Sub

theorem factorization_two_sl2_sq (a : ℕ) (ha : Odd a) (ha1 : 1 < a) :
    ((a ^ 2) * ((a ^ 2) ^ 2 - 1)).factorization 2 = (a * (a ^ 2 - 1)).factorization 2 + 1 := by
  obtain ⟨k, rfl⟩ := ha
  have hk : k ≠ 0 := by omega
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  have h2 : ((2 * k + 1) ^ 2) ^ 2 - 1 = ((2 * k + 1) ^ 2 - 1) * ((2 * k + 1) ^ 2 + 1) := by
    have : (2 * k + 1) ^ 2 ≥ 1 := Nat.one_le_pow _ _ (by omega)
    zify [this, Nat.one_le_pow 2 (2 * k + 1) (by omega), show ((2 * k + 1) ^ 2) ^ 2 ≥ 1 from
      Nat.one_le_pow _ _ this]
    ring
  have h3 : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
  have hodd1 : ¬ 2 ∣ (2 * k + 1) := by omega
  have hodd2 : ¬ 2 ∣ (2 * k ^ 2 + 2 * k + 1) := by omega
  have hk1 : k * (k + 1) ≠ 0 := by positivity
  have hs : (2 * k + 1) ^ 2 - 1 ≠ 0 := by rw [h1]; omega
  have hsq : (2 * k + 1) ^ 2 + 1 ≠ 0 := by omega
  have hodd3 : (2 * k + 1) ^ 2 ≠ 0 := by positivity
  have hne2 : ((2 * k + 1) ^ 2) ^ 2 - 1 ≠ 0 := by
    rw [h2]; exact Nat.mul_ne_zero hs hsq
  rw [Nat.factorization_mul hodd3 hne2, Nat.factorization_mul (by omega) hs, h2,
    Nat.factorization_mul hs hsq, h3, Nat.factorization_mul (by norm_num) (by omega)]
  have e1 : (2 * k + 1).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hodd1
  have e2 : ((2 * k + 1) ^ 2).factorization 2 = 0 := by
    rw [Nat.factorization_pow]; simp [e1]
  have e3 : (2 * k ^ 2 + 2 * k + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd2
  simp [e1, e3, Nat.Prime.factorization_self Nat.prime_two]

section Card

variable {F : Type} [Field F] [Finite F]

theorem natCard_fixField {σ : F ≃+* F} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Nat.card F = Nat.card (fixField σ) ^ 2 := by
  have h := nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  have hord : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  rw [hord] at h
  exact h

theorem ringChar_ne_two_of_odd (hF : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  intro h
  apply h2
  have : (2 : F) = ((ringChar F : ℕ) : F) := by rw [h]; norm_num
  rw [this]
  exact ringChar.Nat.cast_ringChar

theorem odd_natCard_fixField (hF : Odd (Nat.card F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) : Odd (Nat.card (fixField σ)) := by
  have h := natCard_fixField hσ2 hσ1
  rw [h] at hF
  exact Nat.Odd.of_mul_right (by rwa [← pow_two])

theorem natCard_sylow_eq_two_mul {σ : F ≃+* F} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hF : Odd (Nat.card F)) (Q : Sylow 2 SL(2, F)) (Q₀ : Sylow 2 SL(2, fixField σ)) :
    Nat.card Q = 2 * Nat.card Q₀ := by
  have hq := natCard_fixField hσ2 hσ1
  have hodd := odd_natCard_fixField hF hσ2 hσ1
  have hgt : 1 < Nat.card (fixField σ) := Finite.one_lt_card
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, card_sl2_eq, card_sl2_eq, hq,
    factorization_two_sl2_sq _ hodd hgt, pow_succ, mul_comm]

end Card

section Quat

variable {F : Type} [Field F] [Finite F]

theorem quaternion_of_sylow_fix (hF : Odd (Nat.card F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) (γ : MulAut SL(2, F)) {Ph : Subgroup SL(2, F)}
    (hle : Ph ≤ fixSub (γ * slFieldAut F σ * γ⁻¹))
    (hcard : Nat.card Ph = 2 ^ (Nat.card (fixSub (γ * slFieldAut F σ * γ⁻¹))).factorization 2)
    (Q : Sylow 2 SL(2, F)) :
    (∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥Ph ≃* QuaternionGroup (2 ^ k))) ∧
      2 * Nat.card Ph = Nat.card Q := by
  classical
  have hθinj := thetaF_injective σ
  have hfix : fixSub (γ * slFieldAut F σ * γ⁻¹) =
      (thetaF σ).range.map (γ : SL(2, F) →* SL(2, F)) := by
    rw [fixSub_conj, range_thetaF]
  have hcardfix : Nat.card (fixSub (γ * slFieldAut F σ * γ⁻¹)) = Nat.card SL(2, fixField σ) := by
    rw [hfix, Subgroup.card_map_of_injective γ.injective,
      ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
  set Ph' : Subgroup SL(2, F) := Ph.map (γ⁻¹ : MulAut SL(2, F)).toMonoidHom with hPh'
  have hPh'le : Ph' ≤ (thetaF σ).range := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hle hx
    rw [hfix] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have : (γ⁻¹ : MulAut SL(2, F)) x = y := by
      rw [← hyx]
      simp
    exact this ▸ hy
  set Q₀ : Subgroup SL(2, fixField σ) := Ph'.comap (thetaF σ) with hQ₀
  have hQ₀map : Q₀.map (thetaF σ) = Ph' := Subgroup.map_comap_eq_self hPh'le
  have hQ₀card : Nat.card Q₀ = Nat.card Ph := by
    have h1 : Nat.card (Q₀.map (thetaF σ)) = Nat.card Q₀ :=
      Subgroup.card_map_of_injective hθinj
    have h2 : Nat.card Ph' = Nat.card Ph := Subgroup.card_map_of_injective (γ⁻¹).injective
    rw [← h1, hQ₀map, h2]
  have hS : Nat.card Q₀ = 2 ^ (Nat.card SL(2, fixField σ)).factorization 2 := by
    rw [hQ₀card, hcard, hcardfix]
  let S₀ : Sylow 2 SL(2, fixField σ) := Sylow.ofCard Q₀ hS
  have hchar : ringChar (fixField σ) ≠ 2 :=
    ringChar_ne_two_of_odd (odd_natCard_fixField hF hσ2 hσ1)
  obtain ⟨k, hk, ⟨eq⟩⟩ := specialLinearGroup_sylow_quaternion (fixField σ) hchar S₀
  have e1 : ↥Ph ≃* ↥Ph' :=
    Subgroup.equivMapOfInjective Ph (γ⁻¹ : MulAut SL(2, F)).toMonoidHom (γ⁻¹).injective
  have e2 : ↥Q₀ ≃* ↥Ph' :=
    (Subgroup.equivMapOfInjective Q₀ (thetaF σ) hθinj).trans (MulEquiv.subgroupCongr hQ₀map)
  refine ⟨⟨k, hk, ⟨e1.trans (e2.symm.trans eq)⟩⟩, ?_⟩
  rw [natCard_sylow_eq_two_mul hσ2 hσ1 hF Q S₀]
  have : Nat.card S₀ = Nat.card Q₀ := rfl
  rw [this, hQ₀card]

end Quat



end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
