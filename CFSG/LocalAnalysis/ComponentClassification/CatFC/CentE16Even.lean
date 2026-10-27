module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Tags
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

open scoped MatrixGroups

theorem e16_even_psl_sixteen {K : Type} [Group K] [Finite K] (D : CatE16Data K)
    (hmod : LieModel K .PSL 2 2 4) (h4 : 2 ^ 4 ∣ Nat.card K) :
    Nat.card (Subgroup.centralizer ({D.κ} : Set K)) = 16 ∧
      ∀ a ∈ Subgroup.centralizer ({D.κ} : Set K), ∀ b ∈ Subgroup.centralizer ({D.κ} : Set K),
        a * b = b * a ∧ a * a = 1 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hmod (by decide)
  have hchar : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  let ε : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hκ'2 : orderOf (ε D.κ) = 2 := by rw [MulEquiv.orderOf_eq]; exact D.hκ2
  have hsq : ∀ x ∈ Subgroup.centralizer ({D.κ} : Set K), x * x = 1 := by
    intro x hx
    have hx' : ε x ∈ Subgroup.centralizer ({ε D.κ} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul, hx]
    have := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo hκ'2 hx'
    apply ε.injective
    rw [map_mul, map_one, ← sq]
    exact this
  have hcomm : ∀ a ∈ Subgroup.centralizer ({D.κ} : Set K),
      ∀ b ∈ Subgroup.centralizer ({D.κ} : Set K), a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (Subgroup.mul_mem _ ha hb)
    have ha' := hsq a ha
    have hb' := hsq b hb
    have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
    have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb'
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [mul_inv_rev, haa, hbb] at this
    exact this.symm
  refine ⟨?_, fun a ha b hb => ⟨hcomm a ha b hb, hsq a ha⟩⟩
  have hp : IsPGroup 2 (Subgroup.centralizer ({D.κ} : Set K)) := fun x =>
    ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hsq x x.2)⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hdvd := (D.two_pow_dvd_card_iff 4).1 h4
  rw [hm] at hdvd
  have hm4 : 4 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hle := D.hQ
  rw [hm] at hle
  have hm4' : m ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hm, show m = 4 by omega]
  norm_num

theorem e16_even (hO : LieOrderFormulasInput) {K : Type} [Group K] [Finite K] (D : CatE16Data K)
    (heven : EvenLieType K) :
    Nat.card (Subgroup.centralizer ({D.κ} : Set K)) = 16 ∧
      ∀ a ∈ Subgroup.centralizer ({D.κ} : Set K), ∀ b ∈ Subgroup.centralizer ({D.κ} : Set K),
        a * b = b * a ∧ a * a = 1 := by
  obtain ⟨t, n, f, hadm, hmod⟩ := heven
  obtain ⟨-, hord, hfac⟩ := hO K t n 2 f hadm hmod
  have hne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hle : lieSylowExponent t n * f ≤ 4 := by
    by_contra h
    apply D.not_two_pow_five_dvd
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne, hfac]
    omega
  rcases e16_even_cases hadm hle with ⟨rfl, rfl, h2 | h3 | h4⟩ | ⟨rfl, rfl, rfl⟩
  · exfalso
    subst h2
    have h1 : lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 2 (2 ^ 2) = 60 := by decide
    rw [h1, h2, mul_one] at hord
    exact D.card_ne_sixty hord
  · exfalso
    subst h3
    have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
    rw [h1, h2, mul_one] at hord
    have := D.sixty_dvd
    rw [hord] at this
    omega
  · subst h4
    refine e16_even_psl_sixteen D hmod ?_
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne, hfac]
    decide
  · exfalso
    have h1 : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide
    have h2 : lieOrderNumerator .PSL 3 (2 ^ 1) = 168 := by decide
    rw [h1, h2, mul_one] at hord
    have := D.sixty_dvd
    rw [hord] at this
    omega

end CFSG.ComponentClassification.CatFC
