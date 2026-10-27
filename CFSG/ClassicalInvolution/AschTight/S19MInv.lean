module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSU

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

@[expose] def InvolutionsConj (G : Type*) [Group G] : Prop :=
  ∀ x y : G, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → ∃ g : G, g * x * g⁻¹ = y

theorem InvolutionsConj.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : InvolutionsConj H) : InvolutionsConj G := by
  intro x y hx hy hx1 hy1
  obtain ⟨g, hg⟩ := h (e x) (e y) (by rw [← map_mul, hx, map_one])
    (by rw [← map_mul, hy, map_one]) (fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)))
    (fun h1 => hy1 (e.injective (h1.trans (map_one e).symm)))
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]

theorem conj_eq_of_mul_eq_mul {G M : Type*} [Group G] [Monoid M] (ρ : G →* M)
    (hρ : Function.Injective ρ) {x y P Q : G} {D : M} (hP : ρ x * ρ P = ρ P * D)
    (hQ : ρ y * ρ Q = ρ Q * D) : (Q * P⁻¹) * x * (Q * P⁻¹)⁻¹ = y := by
  apply hρ
  have e1 : ρ P⁻¹ * ρ P = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : ρ Q * ρ Q⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have key : ρ ((Q * P⁻¹) * x * (Q * P⁻¹)⁻¹) = ρ Q * (ρ P⁻¹ * (ρ x * ρ P)) * ρ Q⁻¹ := by
    simp only [map_mul, mul_inv_rev, inv_inv, mul_assoc]
  rw [key, hP, ← mul_assoc (ρ P⁻¹), e1, one_mul, ← hQ, mul_assoc, e2, mul_one]

abbrev negDiag3 (F : Type*) [Field F] (a : ℕ) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal (fun j : Fin 3 => if j.val < a then (-1 : F) else 1)

theorem eq_two_of_conj_diag {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 3) (Fin 3) F) (hρ : Function.Injective ρ)
    (hdet : ∀ g, (ρ g).det = 1) {x P : G} (hx1 : x ≠ 1) {a : ℕ} (ha : a ≤ 3)
    (hP : ρ x * ρ P = ρ P * negDiag3 F a) : a = 2 := by
  have hd : (negDiag3 F a).det = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, hdet, one_mul, one_mul] at this
    exact this.symm
  have hneg : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination (-1 : F) * h)
  rw [Matrix.det_diagonal, Fin.prod_univ_three] at hd
  interval_cases a
  · exfalso
    apply hx1
    apply hρ
    have hD : negDiag3 F 0 = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
    have e1 : ρ P * ρ P⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hD, mul_one] at hP
    calc ρ x = ρ x * (ρ P * ρ P⁻¹) := by rw [e1, mul_one]
      _ = ρ 1 := by rw [← mul_assoc, hP, e1, map_one]
  · exact absurd (by simpa using hd) hneg
  · rfl
  · exact absurd (by simpa using hd) hneg

theorem involutionsConj_of_diag {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 3) (Fin 3) F) (hρ : Function.Injective ρ)
    (hdet : ∀ g, (ρ g).det = 1)
    (hdiag : ∀ x : G, x * x = 1 → ∃ a ≤ 3, ∃ P : G, ρ x * ρ P = ρ P * negDiag3 F a) :
    InvolutionsConj G := by
  intro x y hx hy hx1 hy1
  obtain ⟨a, ha, P, hP⟩ := hdiag x hx
  obtain ⟨b, hb, Q, hQ⟩ := hdiag y hy
  obtain rfl := eq_two_of_conj_diag h2 ρ hρ hdet hx1 ha hP
  obtain rfl := eq_two_of_conj_diag h2 ρ hρ hdet hy1 hb hQ
  exact ⟨Q * P⁻¹, conj_eq_of_mul_eq_mul ρ hρ hP hQ⟩

theorem involutionsConj_sl3 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    InvolutionsConj SL(3, F) := by
  refine involutionsConj_of_diag h2 Matrix.SpecialLinearGroup.coeMonoidHom
    (fun x y h => Subtype.ext (by simpa using h)) (fun g => by simp) ?_
  intro x hx
  have hD : (x : Matrix (Fin 3) (Fin 3) F) * x = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, ha, P, hP⟩ := ModelFacts.exists_sl_conj_diagonal h2 (by norm_num) hD
  exact ⟨a, ha, P, by simpa using hP⟩

theorem involutionsConj_su3 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) : InvolutionsConj (Su F p f 3) := by
  refine involutionsConj_of_diag h2 (suMatHom F p f 3) suMatHom_injective
    (fun g => det_suMat g) ?_
  intro x hx
  obtain ⟨a, ha, P, hP⟩ := ModelFacts.exists_su_conj_negBlock hF h2 (by norm_num) hx
  refine ⟨a, ha, P, ?_⟩
  rw [suMatHom_apply, suMatHom_apply, hP, ModelFacts.negBlockK_zero_eq_diagonal]

theorem involutionsConj_SU3 {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) :
    InvolutionsConj (Unitary.SU (unitaryInvolution F p f) 3) := by
  obtain ⟨P, hP⟩ := Unitary.exists_wittMatrix hF 3
  exact InvolutionsConj.of_mulEquiv (Unitary.conjEquiv P hP) (involutionsConj_su3 hF h2)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
