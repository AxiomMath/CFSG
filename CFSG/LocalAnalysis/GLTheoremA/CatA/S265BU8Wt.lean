module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Comb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Cube
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Proj
public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes
open Matrix

variable {K : Type} [Field K]

private theorem pow_three_of_diagonal {n : ℕ} {A : GL (Fin n) K} {δ : Fin n → K} (hA : A ^ 3 = 1)
    (hd : (A : Matrix (Fin n) (Fin n) K) = diagonal δ) (l : Fin n) : δ l ^ 3 = 1 := by
  have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) l l) hA
  simp only [Units.val_pow_eq_pow_val, hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
    one_apply_eq, Pi.pow_apply] at e
  exact e

theorem exists_four_eigen (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : n = 5 ∨ n = 6)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {E₀ : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hED : E₀ ≤ primeFormD h (idGram K n)) (hE3 : ∀ c ∈ E₀, c ^ 3 = 1)
    (hEσ : ∀ c ∈ E₀, primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ * c =
      c * primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ)
    (h27 : 27 ≤ Nat.card E₀) {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥)
    (hiso : W ≤ W.orthogonalBilin (idForm h n))
    (hWE : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ →
      ∀ w ∈ W, ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hab : ∀ X Y : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ →
      primeFormConjHom h (idGram K n) Y ∈ E₀ → X * Y = Y * X) :
    ∃ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ ∧
      primeFormConjHom h (idGram K n) X ≠ 1 ∧ X ^ 3 = 1 ∧
      ∃ (R : GL (Fin n) K) (χ : Fin n → K),
        ((R * (X : GL (Fin n) K) * R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal χ ∧
        Nat.card {l // χ l = 1} = 4 := by
  have := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ 2 ^ 3 = 2) := by norm_num
  choose L hL hL3 using fun c : E₀ =>
    exists_cube_lift_of_fieldHom_comm h hn3 hσ (hED c.2) (hE3 _ c.2) (hEσ _ c.2)
  have hLE : ∀ c, primeFormConjHom h (idGram K n) (L c) ∈ E₀ := fun c => by
    rw [hL]
    exact c.2
  obtain ⟨P, hPU, hP⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
    h (by norm_num) (Set.range fun c => (L c : GL (Fin n) K)) (by rintro _ ⟨c, rfl⟩; exact (L c).2)
    (by
      rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
      exact congrArg Subtype.val (hab _ _ (hLE c) (hLE c')))
    (by
      rintro _ ⟨c, rfl⟩
      rw [← Subgroup.coe_pow, hL3, Subgroup.coe_one])
  obtain ⟨d, hD⟩ : ∃ d : E₀ → Fin n → K, ∀ c,
      ((P⁻¹ * (L c : GL (Fin n) K) * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal (d c) :=
    ⟨fun c => diag ((P⁻¹ * (L c : GL (Fin n) K) * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      fun c => (hP _ ⟨c, rfl⟩).diagonal_diag.symm⟩
  have hd3 : ∀ c l, d c l ^ 3 = 1 := fun c => by
    have e := conj_pow (a := P⁻¹) (b := (L c : GL (Fin n) K)) (i := 3)
    rw [inv_inv, ← Subgroup.coe_pow, hL3, Subgroup.coe_one, mul_one, inv_mul_cancel] at e
    exact pow_three_of_diagonal e (hD c)
  have hd0 : ∀ c l, d c l ≠ 0 := fun c l h0 => by simpa [h0] using hd3 c l
  obtain ⟨i, j, hij, hdij⟩ := exists_eq_weight_of_isotropic h (ι := E₀)
    (X := fun c => (L c : GL (Fin n) K)) (R := P⁻¹) (inv_mem hPU) (d := d)
    (fun c => by
      rw [inv_inv]
      exact hD c) hW hiso (fun c w hw => hWE (L c) (hLE c) w hw)
  have hsc : ∀ c c' : E₀, ∃ s : Kˣ, ∀ l, d (c * c') l = s * (d c l * d c' l) := by
    intro c c'
    have h1 : primeFormConjHom h (idGram K n) (L (c * c') * (L c * L c')⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, hL, hL, hL, Subgroup.coe_mul, mul_inv_cancel]
    obtain ⟨s, -, hs⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hs
    have e : P⁻¹ * (L (c * c') : GL (Fin n) K) * P = GeneralLinearGroup.scalar (Fin n) s *
        (P⁻¹ * (L c : GL (Fin n) K) * P * (P⁻¹ * (L c' : GL (Fin n) K) * P)) := by
      rw [mul_inv_eq_iff_eq_mul.1 hs, ← mul_assoc P⁻¹, ← GeneralLinearGroup.scalar_commute s P⁻¹]
      group
    have e' : diagonal (d (c * c')) =
        Matrix.scalar (Fin n) (s : K) * (diagonal (d c) * diagonal (d c')) := by
      rw [← hD, ← hD, ← hD, e, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    refine ⟨s, fun l => ?_⟩
    have e'' := congrFun (congrFun e' l) l
    simp only [Matrix.scalar_apply, diagonal_mul_diagonal, diagonal_apply_eq] at e''
    exact e''
  have hmul : ∀ l (c c' : E₀),
      d (c * c') l / d (c * c') i = d c l / d c i * (d c' l / d c' i) := by
    intro l c c'
    obtain ⟨s, hs⟩ := hsc c c'
    rw [hs, hs, mul_div_mul_left _ _ s.ne_zero, div_mul_div_comm]
  have hpow : ∀ l (c : E₀), (d c l / d c i) ^ 3 = 1 := fun l c => by
    rw [div_pow, hd3, hd3, div_one]
  have hfaith : ∀ c : E₀, (∀ l, d c l / d c i = 1) → c = 1 := by
    intro c hc
    have hPc : P⁻¹ * (L c : GL (Fin n) K) * P =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 (d c i) (hd0 c i)) := by
      refine Units.ext ?_
      rw [hD, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      exact congrArg diagonal (funext fun l => (div_eq_one_iff_eq (hd0 c i)).1 (hc l))
    have hLc : (L c : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 (d c i) (hd0 c i)) :=
      calc (L c : GL (Fin n) K) = P * (P⁻¹ * L c * P) * P⁻¹ := by group
        _ = _ := by rw [hPc, ← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
    exact Subtype.ext (by
      rw [← hL c, primeFormConjHom_eq_one_of_coe_eq_scalar hLc, Subgroup.coe_one])
  obtain ⟨c, hc1, hc4⟩ := exists_four_trivial hn (fun l c => d c l / d c i) hmul hpow h27 hfaith
    hij (fun c => div_self (hd0 c i)) (fun c => by rw [← hdij c, div_self (hd0 c i)])
  have hu3 : Units.mk0 (d c i) (hd0 c i) ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd3, Units.val_one])
  have hu'n : h.norm (((Units.mk0 (d c i) (hd0 c i))⁻¹ : Kˣ) : K) = 1 := by
    rw [← pow_succ_eq_one_iff_norm h, inv_pow, show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, hu3,
      one_pow, inv_one]
  refine ⟨scalarU h n (Units.mk0 (d c i) (hd0 c i))⁻¹ hu'n * L c, ?_, ?_,
    rescale_pow_eq_one hn3 hne hu'n (by rw [← Subgroup.coe_pow, hL3, hu3, map_one,
      Subgroup.coe_one]), P⁻¹, fun l => d c l / d c i, ?_, hc4⟩
  · rw [map_mul, conjHom_scalarU hn3 hne, one_mul]
    exact hLE c
  · rw [map_mul, conjHom_scalarU hn3 hne, one_mul, hL]
    exact fun h1 => hc1 (Subtype.ext h1)
  · rw [inv_inv, Subgroup.coe_mul, coe_scalarU,
      show P⁻¹ * (GeneralLinearGroup.scalar (Fin n) (Units.mk0 (d c i) (hd0 c i))⁻¹ *
          (L c : GL (Fin n) K)) * P =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 (d c i) (hd0 c i))⁻¹ *
          (P⁻¹ * (L c : GL (Fin n) K) * P) by
        rw [← mul_assoc P⁻¹, ← GeneralLinearGroup.scalar_commute _ P⁻¹]
        group,
      Units.val_mul, hD, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul_diagonal]
    congr 1
    funext l
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_inv_mul]

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
