module

import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Mat
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

section SL4

variable {p e : ℕ} [Fact p.Prime]

theorem pow_mod_four_eq_one_of_isSquare_neg_one (hp2 : p ≠ 2) (he : e ≠ 0)
    (h : IsSquare (-1 : GaloisField p e)) : p ^ e % 4 = 1 := by
  have := Fintype.ofFinite (GaloisField p e)
  have h1 := FiniteField.isSquare_neg_one_iff.mp h
  have hcard : Fintype.card (GaloisField p e) = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p e he
  rw [hcard] at h1
  have hodd : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨k, hk⟩ := hodd
  omega

theorem sl4_twin_sq {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R')
    (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {x x' : SL(4, F)} (hxR : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    {c : SL(4, F)} (hc : c ∈ Subgroup.center SL(4, F)) (hcc : c * c = x * x') :
    IsSquare (-1 : F) := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroup h2
  have hR'lr := hi'.eq_longRootGroup h2
  have hxx'c : x * x' ∈ Subgroup.center SL(4, F) := by
    rw [← hcc]
    exact mul_mem hc hc
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxx'c
  have hcomm' : x * x' = x' * x := hcomm x hxR x' hx'R'
  have hsq : (x * x') * (x * x') = 1 := by
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm']
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  have hrr : r * r = 1 := by
    have h1 : (Matrix.scalar (Fin 4) r) * (Matrix.scalar (Fin 4) r) = 1 := by
      rw [hrA, ← Matrix.SpecialLinearGroup.coe_mul, hsq, Matrix.SpecialLinearGroup.coe_one]
    have := congrFun (congrFun h1 0) 0
    simpa [Matrix.scalar_apply] using this
  rcases mul_self_eq_one_iff.mp hrr with hr1 | hr1
  · exfalso
    apply hne
    have h1 : x * x' = 1 := by
      apply Subtype.ext
      rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
    have hxx'' : x' = x := by
      rw [← inv_eq_of_mul_eq_one_right hx2]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · obtain ⟨μ, -, hμA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hμμ : μ * μ = -1 := by
      have h1 : (Matrix.scalar (Fin 4) μ) * (Matrix.scalar (Fin 4) μ) =
          Matrix.scalar (Fin 4) r := by
        rw [hμA, ← Matrix.SpecialLinearGroup.coe_mul, hcc, ← hrA]
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.scalar_apply, hr1] using this
    exact ⟨μ, hμμ.symm⟩

theorem psl4_twin_sq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ∀ R ∈ ModelFund p .PSL 4 e, ∀ R' ∈ ModelFund p .PSL 4 e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .PSL 4 p e Fact.out).K, c * c = x * x' →
          p ^ e % 4 = 1 := by
  intro R hR R' hR' hne hcomm x hxR x' hx'R' hx2 hx1 hx'2 hx'1 c hc hcc
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hfund := CFSG.ClassicalInvolution.RouteD.Exotic.fundamentalSubgroups_psl_eq (p := p)
    (f := e) (m := 3) (by norm_num)
  have hR1 : R ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num) := by
    rw [← hfund]
    exact hR
  have hR1' : R' ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num) := by
    rw [← hfund]
    exact hR'
  exact pow_mod_four_eq_one_of_isSquare_neg_one hp2 he
    (sl4_twin_sq h2 hR1 hR1' hne hcomm hxR hx2 hx1 hx'R' hx'2 hx'1 hc hcc)

end SL4

section SU4

variable {p e : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

theorem su4_twin_sq {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {x x' : Su K p f 4}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) {c : Su K p f 4} (hc : c ∈ Subgroup.center (Su K p f 4))
    (hcc : c * c = x * x') : p ^ f % 4 = 3 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two hK hp hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two hK hp hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroupSU h2
  have hR'lr := hi'.eq_longRootGroupSU h2
  have hxx'c : x * x' ∈ Subgroup.center (Su K p f 4) := by
    rw [← hcc]
    exact mul_mem hc hc
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hxx'c
  have hr' : suMat (x * x') = Matrix.scalar (Fin 4) (r : K) := hr
  have hcomm' : x * x' = x' * x := hcomm x hxR x' hx'R'
  have hsq : (x * x') * (x * x') = 1 := by
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm']
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  have hrr : (r : K) * r = 1 := by
    have h1 : suMat (x * x') * suMat (x * x') = 1 := by rw [← suMat_mul, hsq, suMat_one]
    rw [hr'] at h1
    have h3 : (Matrix.scalar (Fin 4) (r : K)) * Matrix.scalar (Fin 4) (r : K) = 1 := h1
    have := congrFun (congrFun h3 0) 0
    simpa [Matrix.scalar_apply] using this
  rcases mul_self_eq_one_iff.mp hrr with hr1 | hr1
  · exfalso
    apply hne
    have h1 : x * x' = 1 := by
      apply suMat_injective
      rw [hr', hr1, suMat_one]
      simp
    have hxx'' : x' = x := by
      rw [← inv_eq_of_mul_eq_one_right hx2]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · obtain ⟨u, hu⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hc
    have hu' : suMat c = Matrix.scalar (Fin 4) (u : K) := hu
    have huu : (u : K) * u = -1 := by
      have h1 : suMat c * suMat c = suMat (x * x') := by rw [← suMat_mul, hcc]
      rw [hu', hr', hr1] at h1
      have h3 : (Matrix.scalar (Fin 4) (u : K)) * Matrix.scalar (Fin 4) (u : K) =
          Matrix.scalar (Fin 4) (-1 : K) := h1
      have := congrFun (congrFun h3 0) 0
      simpa [Matrix.scalar_apply] using this
    have hunit : conjTr (unitaryInvolution K p f) (suMat c) * suMat c = 1 := c.2.2
    rw [hu'] at hunit
    have hσu : (u : K) ^ p ^ f * u = 1 := by
      have := congrFun (congrFun hunit 0) 0
      simpa [conjTr, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        Fin.sum_univ_four, unitaryInvolution_apply, iterateFrobenius_def] using this
    have hord : orderOf (u : K) = 4 := by
      have h4 : (u : K) ^ 2 ^ (1 + 1) = 1 := by
        calc (u : K) ^ 2 ^ (1 + 1) = ((u : K) * u) * ((u : K) * u) := by ring
          _ = 1 := by rw [huu]; norm_num
      have h2' : ¬ (u : K) ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two, huu]
        intro h
        exact h2 (by linear_combination -h)
      have := orderOf_eq_prime_pow h2' h4
      simpa using this
    have hdvd : 4 ∣ p ^ f + 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_succ]; exact hσu)
    have hodd : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp).pow
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hodd
    omega

theorem psu4_twin_sq (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU 4 p e) :
    ∀ R ∈ ModelFund p .PSU 4 e, ∀ R' ∈ ModelFund p .PSU 4 e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K, c * c = x * x' →
          p ^ e % 4 = 3 := by
  intro R hR R' hR' hne hcomm x hxR x' hx'R' hx2 hx1 hx'2 hx'1 c hc hcc
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hR1 := (hφ R).mp hR
  have hR1' := (hφ R').mp hR'
  have hne1 : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hcomm1 : ∀ a ∈ R.map φ.toMonoidHom, ∀ b ∈ R'.map φ.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a0, ha0, rfl⟩ _ ⟨b0, hb0, rfl⟩
    show φ a0 * φ b0 = φ b0 * φ a0
    rw [← map_mul, ← map_mul, hcomm a0 ha0 b0 hb0]
  have hx1m : φ x ∈ R.map φ.toMonoidHom := ⟨x, hxR, rfl⟩
  have hx1m' : φ x' ∈ R'.map φ.toMonoidHom := ⟨x', hx'R', rfl⟩
  exact su4_twin_sq (K := GaloisField p (2 * e)) hK hp2 hR1 hR1' hne1 hcomm1 hx1m
    (by rw [← map_mul, hx2, map_one]) (by simpa using hx1) hx1m'
    (by rw [← map_mul, hx'2, map_one]) (by simpa using hx'1)
    ((MulEquivClass.apply_mem_center_iff φ).mpr hc) (by rw [← map_mul, ← map_mul, hcc])

end SU4

section Sp4

variable {p e : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras

theorem sp4_twin_sq_false {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    {c : StatedSp 2 F} (hc : c ∈ Subgroup.center (StatedSp 2 F)) (hcc : c * c = x * x') :
    False := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroup h2
  have hR'lr := hi'.eq_longRootGroup h2
  have hxx'c : x * x' ∈ Subgroup.center (StatedSp 2 F) := by
    rw [← hcc]
    exact mul_mem hc hc
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hxx'c
  have hr' : mat 2 F (x * x') = Matrix.scalar _ (r : F) := by
    rw [mat_apply, hr, Matrix.GeneralLinearGroup.coe_scalar]
  have hcomm' : x * x' = x' * x := hcomm x hxR x' hx'R'
  have hsq : (x * x') * (x * x') = 1 := by
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm']
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  have hrr : (r : F) * r = 1 := by
    have h1 : mat 2 F (x * x') * mat 2 F (x * x') = 1 := by rw [← map_mul, hsq, map_one]
    rw [hr'] at h1
    have h3 : (Matrix.scalar (Fin 2 ⊕ Fin 2) (r : F)) * Matrix.scalar (Fin 2 ⊕ Fin 2) (r : F) =
        1 := h1
    have := congrFun (congrFun h3 (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply] using this
  rcases mul_self_eq_one_iff.mp hrr with hr1 | hr1
  · apply hne
    have h1 : x * x' = 1 := by
      apply mat_injective
      rw [hr', hr1, map_one]
      simp
    have hxx'' : x' = x := by
      rw [← inv_eq_of_mul_eq_one_right hx2]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · obtain ⟨ρ, hρ⟩ := exists_scalar_of_mem_center hc
    have hρ' : mat 2 F c = Matrix.scalar _ (ρ : F) := by
      rw [mat_apply, hρ, Matrix.GeneralLinearGroup.coe_scalar]
    have hρρ : (ρ : F) * ρ = -1 := by
      have h1 : mat 2 F c * mat 2 F c = mat 2 F (x * x') := by rw [← map_mul, hcc]
      rw [hρ', hr', hr1] at h1
      have h3 : (Matrix.scalar (Fin 2 ⊕ Fin 2) (ρ : F)) * Matrix.scalar (Fin 2 ⊕ Fin 2) (ρ : F) =
          Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : F) := h1
      have := congrFun (congrFun h3 (Sum.inl 0)) (Sum.inl 0)
      simpa [Matrix.scalar_apply] using this
    have hsp := mat_transpose_mul_gram_mul c
    rw [hρ'] at hsp
    have := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
    simp [Matrix.scalar_apply, gram, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    have h4 : (-1 : F) = 1 := by rw [← hρρ]; exact this
    exact h2 (by linear_combination -h4)

theorem psp2_twin_no_sq (hp2 : p ≠ 2) (_hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) :
    ∀ R ∈ ModelFund p .PSp 2 e, ∀ R' ∈ ModelFund p .PSp 2 e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, ∀ x' ∈ R', x * x = 1 → x ≠ 1 → x' * x' = 1 → x' ≠ 1 →
        ∀ c ∈ Subgroup.center (modelUniv .PSp 2 p e Fact.out).K, c * c = x * x' → False := by
  intro R hR R' hR' hne hcomm x hxR x' hx'R' hx2 hx1 hx'2 hx'1 c hc hcc
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  exact sp4_twin_sq_false h2
    ((CFSG.ClassicalInvolution.ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).mp hR)
    ((CFSG.ClassicalInvolution.ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').mp hR') hne hcomm
    hxR hx2 hx1 hx'R' hx'2 hx'1 hc hcc

end Sp4

end CFSG.ClassicalInvolution.Asc77.T7H
