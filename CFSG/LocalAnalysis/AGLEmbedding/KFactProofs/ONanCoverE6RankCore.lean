module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverE6

open CFSG.RankThree.CentralCover CFSG.RankThree.Classical2 Polynomial

theorem four_le_pRank_of_inverter_data {K T : Type*} [Group K] [Finite K] [Group T]
    (φ : K →* T) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K)
    (h w : Fin 4 → T) (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨hDab, hDcard, hF⟩ := inversion_basis_package hφ hker Nat.prime_three (by norm_num) h w
    hcomm hord hinv hfix
  rw [Fintype.card_fin] at hDcard
  obtain ⟨V, -, hVab, hVcard, -⟩ := exists_elemAbelian_le_centralizer hφ hker Nat.prime_three
    (by norm_num) (D := Subgroup.closure (Set.range h)) hDab.2 hF (r := 4) (by rw [hDcard])
    (u := 1) (by simp) (by simp)
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hVab hVcard

theorem exists_sq_add_mul_add_sq (F : Type) [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    ∃ a b : F, a ^ 2 + a * b + b ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  by_cases h2 : ringChar F = 2
  · have : CharP F 2 := ringChar.of_eq h2
    refine ⟨1, 0, ?_⟩
    simp [CharTwo.neg_eq]
  · have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hodd : Fintype.card F % 2 = 1 := by
      rcases FiniteField.card F (ringChar F) with ⟨n, hp, hn⟩
      have : Fact (ringChar F).Prime := ⟨hp⟩
      rw [hn]
      exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left h2).pow)
    have h4' : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2' h2'
    have h4 : (3 / 4 : F) ≠ 0 := div_ne_zero h3 h4'
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
      (f := (X ^ 2 + C 1 : F[X])) (g := (C (3 / 4 : F) * X ^ 2 : F[X]))
      (by rw [degree_X_pow_add_C (by norm_num)]; rfl)
      (by rw [degree_C_mul h4, degree_X_pow]; rfl) hodd
    refine ⟨x - y / 2, y, ?_⟩
    simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at hxy
    have : (x - y / 2) ^ 2 + (x - y / 2) * y + y ^ 2 = x ^ 2 + 3 / 4 * y ^ 2 := by
      field_simp
      ring
    rw [this]
    linear_combination hxy

theorem exists_order_three_inverter (F : Type) [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    ∃ e u : Matrix.SpecialLinearGroup (Fin 2) F, e ≠ 1 ∧ e ^ 3 = 1 ∧ u * e * u⁻¹ = e⁻¹ := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_mul_add_sq F h3
  let E : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1]
  let U : Matrix (Fin 2) (Fin 2) F := !![a, b; a + b, -a]
  have hE : E.det = 1 := by simp [E, Matrix.det_fin_two]
  have hU : U.det = 1 := by
    simp [U, Matrix.det_fin_two]
    linear_combination -hab
  let e : Matrix.SpecialLinearGroup (Fin 2) F := ⟨E, hE⟩
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨U, hU⟩
  have he3 : e * (e * e) = 1 := by
    apply Subtype.ext
    show E * (E * E) = 1
    simp [E, Matrix.one_fin_two]
  have hinv : e⁻¹ = e * e := inv_eq_of_mul_eq_one_right he3
  refine ⟨e, u, ?_, by rw [pow_succ, pow_succ, pow_one, mul_assoc]; exact he3, ?_⟩
  · intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [e, E] at this
  · rw [hinv, mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    show U * E = (E * E) * U
    simp [E, U]
    ring

theorem commute_of_sup {G : Type*} [Group G] {A₁ A₂ B₁ B₂ : Subgroup G}
    (h11 : ∀ x ∈ A₁, ∀ y ∈ B₁, Commute x y) (h12 : ∀ x ∈ A₁, ∀ y ∈ B₂, Commute x y)
    (h21 : ∀ x ∈ A₂, ∀ y ∈ B₁, Commute x y) (h22 : ∀ x ∈ A₂, ∀ y ∈ B₂, Commute x y) :
    ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ B₁ ⊔ B₂, Commute x y := by
  have key : ∀ x : G, (∀ y ∈ B₁, Commute x y) → (∀ y ∈ B₂, Commute x y) →
      ∀ y ∈ B₁ ⊔ B₂, Commute x y := by
    intro x hx1 hx2 y hy
    have hle : B₁ ⊔ B₂ ≤ Subgroup.centralizer {x} := sup_le
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hx1 y hy).symm.eq)
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hx2 y hy).symm.eq)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hle : A₁ ⊔ A₂ ≤ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      exact (key x (h11 x hx) (h12 x hx) y hy).symm.eq
    · refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      exact (key x (h21 x hx) (h22 x hx) y hy).symm.eq
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

end CFSG.AGLEmbedding.KFactProofs.CoverE6
