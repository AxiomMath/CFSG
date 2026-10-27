module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section
namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open Matrix CFSG.RankThree.Classical2 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

theorem not_forall_unitary_conj_frobenius_shift
    {L : Type} [Field L] [CharP L 2]
    (sigma eta : L →+* L) (w : Lˣ) (hw : orderOf w = 9)
    (hbar : Units.map sigma.toMonoidHom w = w⁻¹)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (heta : ∀ c, eta c = c ^ (2 ^ k))
    (B : GL (Fin 3) L) (eps : Bool) :
    ¬ ∀ X : SL(3, L), stdUnitary sigma X = X →
      conjSLn B (if eps then stdUnitary eta X else Matrix.SpecialLinearGroup.map eta X) = X := by
  let D : SL(3, L) :=
    Matrix.SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 2 by decide) (w : L) w.ne_zero *
      Matrix.SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 2 by decide) (w : L) w.ne_zero
  have hD : (D : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![(w : L), (w : L), (((w⁻¹ : Lˣ) : L) ^ 2)] := by
    dsimp only [D]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.diag2n_coe,
      Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [pow_two]
  have hInv (rho : L →+* L) : ((D : Matrix (Fin 3) (Fin 3) L).map rho)⁻¹ =
      Matrix.diagonal ![(rho (w : L))⁻¹, (rho (w : L))⁻¹, (rho (w : L)) ^ 2] := by
    rw [hD, Matrix.diagonal_map (map_zero rho)]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    have hne : rho (w : L) ≠ 0 := (map_ne_zero rho).mpr w.ne_zero
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> simp [map_pow, map_inv₀, hne, pow_two] <;> field_simp
    · simp [Matrix.diagonal, hij]
  have hFix : stdUnitary sigma D = D := by
    have hb : sigma (w : L) = (((w⁻¹ : Lˣ) : L)) :=
      congrArg (fun x : Lˣ => (x : L)) hbar
    apply Subtype.ext
    rw [coe_stdUnitary, hInv sigma, Matrix.diagonal_transpose, hD]
    congr 1
    funext i
    fin_cases i <;> simp [hb]
  have hTr : Matrix.trace (D : Matrix (Fin 3) (Fin 3) L) = (((w⁻¹ : Lˣ) : L) ^ 2) := by
    rw [hD, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp [CharTwo.add_self_eq_zero]
  have hT : Matrix.trace
      ((if eps then stdUnitary eta D else Matrix.SpecialLinearGroup.map eta D : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) =
      if eps then (w : L) ^ (2 * 2 ^ k) else (((w⁻¹ : Lˣ) : L) ^ (2 * 2 ^ k)) := by
    cases eps with
    | false =>
      change Matrix.trace ((Matrix.SpecialLinearGroup.map eta D : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = (((w⁻¹ : Lˣ) : L) ^ (2 * 2 ^ k))
      change Matrix.trace ((D : Matrix (Fin 3) (Fin 3) L).map eta) = _
      rw [hD,
        Matrix.diagonal_map (map_zero eta), Matrix.trace_diagonal, Fin.sum_univ_three]
      simp [CharTwo.add_self_eq_zero, heta, pow_mul]
    | true =>
      change Matrix.trace ((stdUnitary eta D : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = (w : L) ^ (2 * 2 ^ k)
      rw [coe_stdUnitary, hInv eta, Matrix.diagonal_transpose, Matrix.trace_diagonal, Fin.sum_univ_three]
      simp [CharTwo.add_self_eq_zero, heta, inv_pow, inv_inv, pow_mul]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  intro h
  have hEq := congrArg (fun X : SL(3, L) => Matrix.trace (X : Matrix (Fin 3) (Fin 3) L))
    (h D hFix)
  rw [coe_conjSLn, Matrix.trace_units_conj, hT, hTr] at hEq
  cases eps with
  | false =>
    have hPow : (w⁻¹) ^ (2 * 2 ^ k) = (w⁻¹) ^ 2 := by
      apply Units.ext
      simpa using hEq
    rw [pow_inj_mod, orderOf_inv, hw] at hPow
    rcases hk with rfl | rfl <;> norm_num at hPow
  | true =>
    have hPow : w ^ (2 * 2 ^ k) = (w⁻¹) ^ 2 := by
      apply Units.ext
      simpa using hEq
    have hOne : w ^ (2 * 2 ^ k + 2) = 1 := by
      rw [pow_add, hPow, ← mul_pow, inv_mul_cancel, one_pow]
    have hDiv := orderOf_dvd_of_pow_eq_one hOne
    rw [hw] at hDiv
    rcases hk with rfl | rfl <;> norm_num at hDiv

theorem not_forall_unitary_frame_conj_frobenius_shift
    {L : Type} [Field L] [CharP L 2] (sigma eta : L ≃+* L)
    (w : Lˣ) (hw : orderOf w = 9)
    (hbar : Units.map sigma.toRingHom.toMonoidHom w = w⁻¹)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (heta : ∀ c, eta c = c ^ (2 ^ k))
    {H : Type*} [Group H] (psi : SL(3, L) →* H)
    (hker : psi.ker ≤ Subgroup.center SL(3, L))
    (hperf : Group.IsPerfect (CFSG.RankThree.Classical2.fixSubgroup
      (stdUnitaryEquiv (ν := 3) sigma)))
    (B : GL (Fin 3) L) (eps : Bool) :
    ¬ ∀ X : SL(3, L), stdUnitary sigma.toRingHom X = X →
      psi (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
        (if eps then stdUnitary eta.toRingHom X else Matrix.SpecialLinearGroup.map eta.toRingHom X)) = psi X := by
  intro h
  let C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) sigma)
  let T : SL(3, L) →* SL(3, L) :=
    if eps then stdUnitary eta.toRingHom else Matrix.SpecialLinearGroup.map eta.toRingHom
  let a : C →* SL(3, L) :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B).toMonoidHom.comp
      (T.comp C.subtype)
  have heq : ∀ X : C, a X = C.subtype X :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq psi hker hperf a C.subtype
      (fun X => by
        have hX : stdUnitary sigma.toRingHom (X : SL(3, L)) = (X : SL(3, L)) := by
          simpa only [C, CFSG.RankThree.Classical2.mem_fixSubgroup,
            stdUnitaryEquiv_apply] using X.property
        have hT : T (X : SL(3, L)) =
            (if eps then stdUnitary eta.toRingHom (X : SL(3, L))
              else Matrix.SpecialLinearGroup.map eta.toRingHom (X : SL(3, L))) := by
          cases eps <;> rfl
        change psi (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
          (T (X : SL(3, L)))) = psi (X : SL(3, L))
        rw [hT]
        exact h (X : SL(3, L)) hX)

  apply not_forall_unitary_conj_frobenius_shift sigma.toRingHom eta.toRingHom w hw hbar k hk heta B eps
  intro X hX
  have hm : X ∈ C := by
    simpa only [C, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply] using hX
  have hEq := congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (heq ⟨X, hm⟩)
  apply Subtype.ext
  change _ = (X : Matrix (Fin 3) (Fin 3) L)
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  have hT : T X = (if eps then stdUnitary eta.toRingHom X else Matrix.SpecialLinearGroup.map eta.toRingHom X) := by
    cases eps <;> rfl
  change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B (T X) : SL(3, L)) :
    Matrix (Fin 3) (Fin 3) L) = X at hEq
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hT] at hEq
  exact hEq

end CFSG.HardMathSupport.Timmesfeld.LangTorus
