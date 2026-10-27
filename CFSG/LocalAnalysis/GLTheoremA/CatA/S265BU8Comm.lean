module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Comb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Cube
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Heis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.GLTheoremA.HDescUniRes
open Matrix

variable {K : Type} [Field K]

private theorem eq_of_scalar_mul_eq {n : ℕ} (hn : 0 < n) {a b : Kˣ} {g : GL (Fin n) K}
    (e : GeneralLinearGroup.scalar (Fin n) a * g = GeneralLinearGroup.scalar (Fin n) b * g) :
    a = b := by
  have e' := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩)
    (mul_right_cancel e)
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e'
  exact Units.ext e'

private theorem conj_scalar_mul {n : ℕ} (g t : GL (Fin n) K) (u : Kˣ) :
    g * (GeneralLinearGroup.scalar (Fin n) u * t) * g⁻¹ =
      GeneralLinearGroup.scalar (Fin n) u * (g * t * g⁻¹) := by
  rw [← mul_assoc g, ← GeneralLinearGroup.scalar_commute u g]
  group

private theorem exists_comm_char {ℓ f : ℕ} {h : UnitaryFieldData ℓ f K} {n : ℕ} (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {E₀ : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hED : E₀ ≤ primeFormD h (idGram K n)) (hEc : ∀ c ∈ E₀, ∀ d ∈ E₀, c * d = d * c)
    (hE3 : ∀ c ∈ E₀, c ^ 3 = 1) {T : primeFormUnitary h (idGram K n)}
    (hT : primeFormConjHom h (idGram K n) T ∈ E₀) :
    ∃ κ : E₀ → K, (∀ e e', κ (e * e') = κ e * κ e') ∧ (∀ e, κ e ^ 3 = 1) ∧
      ∀ (e : E₀) (A : primeFormUnitary h (idGram K n)), primeFormConjHom h (idGram K n) A = e →
        κ e = 1 → A * T = T * A := by
  have hlift : ∀ e : E₀, ∃ A : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A = e := fun e => by
    obtain ⟨A, hA⟩ := hED e.2
    exact ⟨A, hA⟩
  choose L hL using hlift
  have hsc : ∀ e : E₀, ∃ c : Kˣ, ((L e : GL (Fin n) K) * T * (L e : GL (Fin n) K)⁻¹) =
      GeneralLinearGroup.scalar (Fin n) c * T := fun e => by
    have h1 : primeFormConjHom h (idGram K n) (L e * T * (L e)⁻¹ * T⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hL, hEc _ e.2 _ hT, mul_inv_cancel_right,
        mul_inv_cancel]
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    exact ⟨c, by rw [← hc]; group⟩
  choose κ hκ using hsc
  have hP : ∀ (e : E₀) (A : primeFormUnitary h (idGram K n)),
      primeFormConjHom h (idGram K n) A = e →
      (A : GL (Fin n) K) * T * (A : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) (κ e) * T := by
    intro e A hA
    have hz : primeFormConjHom h (idGram K n) (A * (L e)⁻¹) = 1 := by
      rw [map_mul, map_inv, hA, hL, mul_inv_cancel]
    have hcz := (commute_of_mem_ker_of_ne hn hne hz (L e * T * (L e)⁻¹)).eq
    have hU : A * T * A⁻¹ = L e * T * (L e)⁻¹ :=
      calc A * T * A⁻¹ = A * (L e)⁻¹ * (L e * T * (L e)⁻¹) * (A * (L e)⁻¹)⁻¹ := by group
        _ = L e * T * (L e)⁻¹ := by rw [hcz]; group
    have hG := congrArg (fun g : primeFormUnitary h (idGram K n) => (g : GL (Fin n) K)) hU
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hG
    rw [hG]
    exact hκ e
  have hmul : ∀ e e', κ (e * e') = κ e * κ e' := fun e e' => by
    have h1 := hP (e * e') (L e * L e') (by rw [map_mul, hL, hL, Subgroup.coe_mul])
    rw [Subgroup.coe_mul, show (L e : GL (Fin n) K) * L e' * T * ((L e : GL (Fin n) K) * L e')⁻¹ =
        (L e : GL (Fin n) K) * ((L e' : GL (Fin n) K) * T * (L e' : GL (Fin n) K)⁻¹) *
          (L e : GL (Fin n) K)⁻¹ by group, hκ e', conj_scalar_mul, hκ e, ← mul_assoc,
      ← map_mul] at h1
    rw [eq_of_scalar_mul_eq (by omega) h1.symm, mul_comm]
  have h1 : κ 1 = 1 := by
    have e := hP 1 1 (by rw [map_one]; rfl)
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one] at e
    have e2 : GeneralLinearGroup.scalar (Fin n) (κ 1) * (T : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) 1 * (T : GL (Fin n) K) := by
      rw [← e, map_one, one_mul]
    exact eq_of_scalar_mul_eq (by omega) e2
  refine ⟨fun e => (κ e : K), fun e e' => (congrArg Units.val (hmul e e')).trans
    (Units.val_mul _ _), fun e => ?_, fun e A hA he => Subtype.ext ?_⟩
  · have he3 : e * e * e = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← pow_three', hE3 _ e.2, Subgroup.coe_one])
    show (κ e : K) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, pow_three', ← hmul, ← hmul, he3, h1, Units.val_one]
  · have e1 := hP e A hA
    rw [show κ e = 1 from Units.ext he, map_one, one_mul] at e1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← inv_mul_cancel_right ((A : GL (Fin n) K) * T) A,
      e1]

theorem mul_comm_of_isotropic_stable (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : n = 5 ∨ n = 6)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {E₀ : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hED : E₀ ≤ primeFormD h (idGram K n)) (hE3 : ∀ c ∈ E₀, c ^ 3 = 1)
    (hEc : ∀ c ∈ E₀, ∀ d ∈ E₀, c * d = d * c)
    (hEσ : ∀ c ∈ E₀, primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ * c =
      c * primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ)
    (h27 : 27 ≤ Nat.card E₀) {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥)
    (hiso : W ≤ W.orthogonalBilin (idForm h n))
    (hWE : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ →
      ∀ w ∈ W, ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    ∀ X Y : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ →
      primeFormConjHom h (idGram K n) Y ∈ E₀ → X * Y = Y * X := by
  have := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have hcube : ∀ X₁ Y₁ : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X₁ ∈ E₀ →
      primeFormConjHom h (idGram K n) Y₁ ∈ E₀ → X₁ ^ 3 = 1 → X₁ * Y₁ = Y₁ * X₁ := by
    intro X₁ Y₁ hX hY hX3
    by_contra hXY
    obtain ⟨κ₁, hm₁, h3₁, hk₁⟩ := exists_comm_char hn3 hne hED hEc hE3 hX
    obtain ⟨κ₂, hm₂, h3₂, hk₂⟩ := exists_comm_char hn3 hne hED hEc hE3 hY
    obtain ⟨e, he1, he₁, he₂⟩ := exists_common_trivial hm₁ hm₂ h3₁ h3₂ (by omega)
    obtain ⟨Z, hZ, hZ3⟩ := exists_cube_lift_of_fieldHom_comm h hn3 hσ (hED e.2) (hE3 _ e.2)
      (hEσ _ e.2)
    have h1 : primeFormConjHom h (idGram K n) (X₁ * Y₁ * X₁⁻¹ * Y₁⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hEc _ hX _ hY, mul_inv_cancel_right,
        mul_inv_cancel]
    obtain ⟨ω, -, hω⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hω
    have hXYω : (X₁ : GL (Fin n) K) * Y₁ = GeneralLinearGroup.scalar (Fin n) ω * (Y₁ * X₁) := by
      rw [← hω]
      group
    refine false_of_heisenberg_isotropic h (by norm_num) (by omega) hX3 hZ3
      (hk₁ e Z hZ he₁).symm (hk₂ e Z hZ he₂).symm (fun hω1 => hXY (Subtype.ext ?_)) hXYω
      (fun c hc => he1 (Subtype.ext ?_)) hW hiso (hWE X₁ hX) (hWE Z (by rw [hZ]; exact e.2))
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, hXYω, hω1, map_one, one_mul]
    · rw [← hZ, primeFormConjHom_eq_one_of_coe_eq_scalar hc, Subgroup.coe_one]
  intro X Y hX hY
  obtain ⟨X₁, hX₁, hX₁3⟩ := exists_cube_lift_of_fieldHom_comm h hn3 hσ (hED hX) (hE3 _ hX)
    (hEσ _ hX)
  obtain ⟨Y₁, hY₁, -⟩ := exists_cube_lift_of_fieldHom_comm h hn3 hσ (hED hY) (hE3 _ hY)
    (hEσ _ hY)
  have h11 := hcube X₁ Y₁ (by rw [hX₁]; exact hX) (by rw [hY₁]; exact hY) hX₁3
  have hz1 : primeFormConjHom h (idGram K n) (X * X₁⁻¹) = 1 := by
    rw [map_mul, map_inv, hX₁, mul_inv_cancel]
  have hz2 : primeFormConjHom h (idGram K n) (Y * Y₁⁻¹) = 1 := by
    rw [map_mul, map_inv, hY₁, mul_inv_cancel]
  have hcomm : Commute (X * X₁⁻¹ * X₁) (Y * Y₁⁻¹ * Y₁) :=
    (commute_of_mem_ker_of_ne hn3 hne hz1 _).mul_left
      ((commute_of_mem_ker_of_ne hn3 hne hz2 X₁).symm.mul_right h11)
  rw [inv_mul_cancel_right, inv_mul_cancel_right] at hcomm
  exact hcomm.eq

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
