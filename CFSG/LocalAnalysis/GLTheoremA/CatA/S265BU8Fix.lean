module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Blk
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim (exists_unitary_isDiag_conj)

variable {K : Type} [Field K]

private theorem card_fixSubfield (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : Nat.card (fixSubfield σ) = 4 :=
  (dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hσ).2.trans (by norm_num)

private theorem map_eq_of_pow_three (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {x : K} (hx : x ^ 3 = 1) : σ x = x := by
  have := h.finite
  have h3 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by rw [card_fixSubfield h hσ] <;> norm_num
  obtain ⟨ω, hω⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd h3
  have hωK : IsPrimitiveRoot (ω : K) 3 := hω.map_of_injective (fixSubfield σ).subtype.injective
  obtain ⟨m, -, rfl⟩ := hωK.eq_pow_of_pow_eq_one hx
  rw [map_pow, (mem_fixSubfield σ).1 ω.2]

section Subfield

variable {f e : ℕ} (h : UnitaryFieldData 2 f K) {k : Subfield K} (h₀ : UnitaryFieldData 2 e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) {n : ℕ}

include hbar in
private theorem mem_unitary_of_subfieldGL {g₀ : GL (Fin n) k}
    (hg : subfieldGL k n g₀ ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g₀ ∈ primeFormUnitary h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, coe_subfieldGL,
    map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul] at hg
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
  refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
  change (((g₀ : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g₀).map k.subtype =
    (1 : Matrix (Fin n) (Fin n) k).map k.subtype
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

include hbar in
private theorem subfieldGL_mem_unitary {g₀ : GL (Fin n) k}
    (hg : g₀ ∈ primeFormUnitary h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    subfieldGL k n g₀ ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one] at hg
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, coe_subfieldGL,
    map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul, hg,
    Matrix.map_one _ (map_zero _) (map_one _)]

end Subfield

private theorem glAut_subfieldGL {σ : K ≃+* K} {n : ℕ} (g₀ : GL (Fin n) (fixSubfield σ)) :
    glAut σ (subfieldGL (fixSubfield σ) n g₀) = subfieldGL (fixSubfield σ) n g₀ := by
  apply Units.ext
  rw [coe_glAut, coe_subfieldGL]
  ext i j
  exact (mem_fixSubfield σ).1 ((g₀ : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

private theorem congr_self {G : Type} [Group G] (ψ α : MulAut G) :
    MulAut.congr ψ α = ψ * α * ψ⁻¹ := by
  ext x
  rfl

theorem glaPLayer_ne_bot_of_four_eigen (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : n = 5 ∨ n = 6)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {X : primeFormUnitary h (idGram K n)} (hX3 : X ^ 3 = 1)
    (hXσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ *
        primeFormConjHom h (idGram K n) X =
      primeFormConjHom h (idGram K n) X *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ)
    {R : GL (Fin n) K} {χ : Fin n → K}
    (hRX : ((R * (X : GL (Fin n) K) * R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal χ)
    (h4 : Nat.card {l // χ l = 1} = 4) :
    GLAPLayer 3 (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K n) X)) ≠ ⊥ := by
  classical
  have := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have hz : primeFormConjHom h (idGram K n)
      (X⁻¹ * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ X) = 1 := by
    rw [map_mul, map_inv,
      ← primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ X, hXσ,
      mul_inv_cancel_right, inv_mul_cancel]
  obtain ⟨lam, -, hlam⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).1 hz
  have hσX : glAut σ (X : GL (Fin n) K) =
      (X : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) lam := by
    rw [← hlam, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, mul_inv_cancel_left]
  obtain ⟨D, hD⟩ : ∃ D : GL (Fin n) K, D = R * (X : GL (Fin n) K) * R⁻¹ := ⟨_, rfl⟩
  rw [← hD] at hRX
  have hD3 : D ^ 3 = 1 := by
    rw [hD, conj_pow, ← Subgroup.coe_pow, hX3, Subgroup.coe_one, mul_one, mul_inv_cancel]
  have hχ3 : ∀ l, χ l ^ 3 = 1 := fun l => by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) l l) hD3
    simp only [Units.val_pow_eq_pow_val, hRX, diagonal_pow, diagonal_apply_eq, Units.val_one,
      one_apply_eq, Pi.pow_apply] at e
    exact e
  have hσD : glAut σ D = D := by
    apply Units.ext
    rw [coe_glAut, hRX, diagonal_map (map_zero σ)]
    exact congrArg diagonal (funext fun l => map_eq_of_pow_three h hσ (hχ3 l))
  obtain ⟨Y, hY⟩ : ∃ Y : GL (Fin n) K, Y = R * (glAut σ R)⁻¹ := ⟨_, rfl⟩
  have hYD : Y * D = GeneralLinearGroup.scalar (Fin n) lam * (D * Y) := by
    have hD' := hσD
    rw [hD, map_mul, map_mul, map_inv, hσX] at hD'
    have hc : R * (X : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) lam =
        GeneralLinearGroup.scalar (Fin n) lam * (R * (X : GL (Fin n) K)) :=
      (GeneralLinearGroup.scalar_commute lam _).symm
    calc Y * D = R * (glAut σ R)⁻¹ * (glAut σ R * ((X : GL (Fin n) K) *
          GeneralLinearGroup.scalar (Fin n) lam) * (glAut σ R)⁻¹) := by rw [hY, hD', hD]
      _ = R * (X : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) lam * (glAut σ R)⁻¹ := by
          group
      _ = GeneralLinearGroup.scalar (Fin n) lam * (R * (X : GL (Fin n) K)) * (glAut σ R)⁻¹ := by
          rw [hc]
      _ = GeneralLinearGroup.scalar (Fin n) lam * (D * Y) := by
          rw [hD, hY]
          group
  have hYm : (Y : Matrix (Fin n) (Fin n) K) * diagonal χ =
      (lam : K) • (diagonal χ * (Y : Matrix (Fin n) (Fin n) K)) := by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hYD
    simp only [Units.val_mul, hRX, GeneralLinearGroup.coe_scalar] at e
    rw [e, Matrix.scalar_apply, smul_eq_diagonal_mul]
  set J : Finset (Fin n) := Finset.univ.filter fun l => χ l = 1
  have hJ4 : J.card = 4 := by rw [← h4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hJ : Jᶜ.card < J.card := by
    rw [Finset.card_compl, hJ4, Fintype.card_fin]
    omega
  have hdet : (Y : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hlam1 : lam = 1 :=
    Units.ext (eq_one_of_mul_diagonal_eq_smul (fun l => by simp [J]) hJ hdet hYm)
  have hσX1 : glAut σ (X : GL (Fin n) K) = X := by rw [hσX, hlam1, map_one, mul_one]
  have h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by decide) hσ
  obtain ⟨X₀, hX₀⟩ := exists_subfieldGL_eq_of_fixed n hσX1
  have hX₀U : X₀ ∈ primeFormUnitary h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
    mem_unitary_of_subfieldGL h h₀ hbar (by rw [hX₀]; exact X.2)
  have hX₀3 : X₀ ^ 3 = 1 := subfieldGL_injective (fixSubfield σ) n (by
    rw [map_pow, hX₀, map_one, ← Subgroup.coe_pow, hX3, Subgroup.coe_one])
  obtain ⟨P₀, hP₀U, hP₀⟩ := exists_unitary_isDiag_conj h₀ (by decide) {X₀}
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hX₀U)
    (fun x hx y hy => by rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy])
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hX₀3)
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin n) K, P = subfieldGL (fixSubfield σ) n P₀ := ⟨_, rfl⟩
  have hPU : P ∈ primeFormUnitary h (idGram K n) := by
    rw [hP]
    exact subfieldGL_mem_unitary h h₀ hbar hP₀U
  have hσP : glAut σ P = P := by rw [hP, glAut_subfieldGL]
  set e : Fin n → K := fun l =>
    (((P₀⁻¹ * X₀ * P₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) l l :
      K)
  have hXe : ((P⁻¹ * (X : GL (Fin n) K) * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal e := by
    rw [hP, ← hX₀, ← map_inv, ← map_mul, ← map_mul, coe_subfieldGL,
      ← (hP₀ X₀ (Set.mem_singleton X₀)).diagonal_diag, diagonal_map (map_zero _)]
    rfl
  have h4e : Nat.card {l // e l = 1} = 4 := by
    have hM : (((P⁻¹ * R⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * diagonal χ =
        diagonal e * ((P⁻¹ * R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← hRX, ← hXe, ← Units.val_mul, ← Units.val_mul, hD]
      congr 1
      group
    have hMdet : ((P⁻¹ * R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [card_fiber_eq_of_support hMdet (fun l k hlk => eq_of_mul_diagonal_eq hM hlk), h4]
  let Pu : primeFormUnitary h (idGram K n) := ⟨P, hPU⟩
  have hfU : primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ Pu = Pu :=
    Subtype.ext (by rw [coe_primeFormFieldU]; exact hσP)
  have hfc := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ Pu
  rw [hfU] at hfc
  have hcomm := mul_inv_eq_iff_eq_mul.1 hfc
  have hfσ : (primeFormConjHom h (idGram K n) Pu)⁻¹ *
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ *
        primeFormConjHom h (idGram K n) Pu =
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ := by
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hL := glaPLayer_ne_bot_of_diagonal_four h hn hσ (X₀ := Pu⁻¹ * X * Pu) (e := e) (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hXe) h4e
  refine S265F3.glaPLayer_ne_bot_of_congr Nat.prime_three
    ((primeFormConjHom h (idGram K n) Pu)⁻¹ : MulAut _) _ _ ?_
  rw [congr_self, congr_self, inv_inv, hfσ, ← map_inv, ← map_mul, ← map_mul]
  exact hL

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
