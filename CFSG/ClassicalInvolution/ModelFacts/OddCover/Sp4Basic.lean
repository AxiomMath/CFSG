module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_equiv_leviHom)
open scoped commutatorElement

section Matrices

variable {K : Type} [Field K]

@[expose] def qMat (S : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 1 S 0 1

theorem qMat_mul (S S' : Matrix (Fin 2) (Fin 2) K) : qMat S * qMat S' = qMat (S + S') := by
  simp [qMat, fromBlocks_multiply, add_comm]

theorem qMat_zero : qMat (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp [qMat]

@[expose] def qGL (S : Matrix (Fin 2) (Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨qMat S, qMat (-S), by rw [qMat_mul, add_neg_cancel, qMat_zero],
    by rw [qMat_mul, neg_add_cancel, qMat_zero]⟩

theorem qGL_mem (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) : qGL S ∈ StatedSp 2 K := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.mem_statedSp_iff]
  simp [qGL, qMat, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, hS]

@[expose] def qSpS (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) : StatedSp 2 K :=
  ⟨qGL S, qGL_mem S hS⟩

theorem mat_qSpS (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) : mat 2 K (qSpS S hS) = qMat S :=
  rfl

theorem qSpS_congr {S S' : Matrix (Fin 2) (Fin 2) K} (h : S = S') (hS : Sᵀ = S) (hS' : S'ᵀ = S') :
    qSpS S hS = qSpS S' hS' := by
  subst h
  rfl

@[expose] noncomputable def lSp (K : Type) [Field K] : GL (Fin 2) K →* StatedSp 2 K :=
  (equivStatedSp 2 K).toMonoidHom.comp (TauCeti.GLSymplecticFin.leviHom (m := 2) (R := K))

theorem mat_lSp (g : GL (Fin 2) K) :
    mat 2 K (lSp K g) = fromBlocks (g : Matrix (Fin 2) (Fin 2) K) 0 0
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
  mat_equiv_leviHom g

theorem lSp_conj_qSpS (g : GL (Fin 2) K) (S : Matrix (Fin 2) (Fin 2) K) (hS : Sᵀ = S) :
    lSp K g * qSpS S hS * (lSp K g)⁻¹ =
      qSpS ((g : Matrix (Fin 2) (Fin 2) K) * S * (g : Matrix (Fin 2) (Fin 2) K)ᵀ) (by
        simp [Matrix.transpose_mul, hS, Matrix.mul_assoc]) := by
  apply mat_injective
  rw [← map_inv (lSp K) g, map_mul, map_mul, mat_lSp, mat_lSp, mat_qSpS, inv_inv]
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ *
      (g : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  generalize ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = gi at h1 h2 ⊢
  simp [qMat, mat_qSpS, fromBlocks_multiply, h1, h2, Matrix.mul_assoc]

@[expose] def symm3 (x y z : K) : Matrix (Fin 2) (Fin 2) K := !![x, y; y, z]

omit [Field K] in
theorem symm3_transpose (x y z : K) : (symm3 x y z)ᵀ = symm3 x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def qSp (x y z : K) : StatedSp 2 K := qSpS (symm3 x y z) (symm3_transpose x y z)

theorem mat_qSp (x y z : K) : mat 2 K (qSp x y z) = qMat (symm3 x y z) := rfl

theorem qSp_mul (x y z x' y' z' : K) :
    qSp x y z * qSp x' y' z' = qSp (x + x') (y + y') (z + z') := by
  apply mat_injective
  rw [map_mul, mat_qSp, mat_qSp, mat_qSp, qMat_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm3]

theorem qSp_zero : qSp (0 : K) 0 0 = 1 := by
  apply mat_injective
  rw [mat_qSp, map_one]
  have : symm3 (0 : K) 0 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symm3]
  rw [this, qMat_zero]

theorem qSp_inv (x y z : K) : (qSp x y z)⁻¹ = qSp (-x) (-y) (-z) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [qSp_mul, add_neg_cancel, add_neg_cancel, add_neg_cancel, qSp_zero]

theorem qSp_comm (x y z x' y' z' : K) : qSp x y z * qSp x' y' z' = qSp x' y' z' * qSp x y z := by
  rw [qSp_mul, qSp_mul, add_comm x, add_comm y, add_comm z]

theorem qSp_injective {x y z x' y' z' : K} (h : qSp x y z = qSp x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have h' := congrArg (fun g : StatedSp 2 K => mat 2 K g) h
  simp only [mat_qSp, qMat, symm3] at h'
  have h1 := congrArg
    (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (Sum.inl 0) (Sum.inr 0)) h'
  have h2 := congrArg
    (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (Sum.inl 0) (Sum.inr 1)) h'
  have h3 := congrArg
    (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (Sum.inl 1) (Sum.inr 1)) h'
  simp at h1 h2 h3
  exact ⟨h1, h2, h3⟩

@[expose] def dGLfun (t : Kˣ × Kˣ) : GL (Fin 2) K :=
  ⟨diagonal ![(t.1 : K), (t.2 : K)], diagonal ![((t.1⁻¹ : Kˣ) : K), ((t.2⁻¹ : Kˣ) : K)], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

@[expose] def dGL : Kˣ × Kˣ →* GL (Fin 2) K where
  toFun := dGLfun
  map_one' := by
    apply Units.ext
    change diagonal ![((1 : Kˣ) : K), ((1 : Kˣ) : K)] = 1
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' t t' := by
    apply Units.ext
    change diagonal ![((t.1 * t'.1 : Kˣ) : K), ((t.2 * t'.2 : Kˣ) : K)] =
      diagonal ![(t.1 : K), (t.2 : K)] * diagonal ![(t'.1 : K), (t'.2 : K)]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_dGL (t : Kˣ × Kˣ) :
    ((dGL t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = diagonal ![(t.1 : K), (t.2 : K)] := rfl

@[expose] def uGL (r : K) : GL (Fin 2) K :=
  ⟨!![1, r; 0, 1], !![1, -r; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_uGL (r : K) : ((uGL r : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, r; 0, 1] :=
  rfl

theorem uGL_add (r r' : K) : uGL (r + r') = uGL r * uGL r' := by
  apply Units.ext
  change !![1, r + r'; 0, 1] = !![1, r; 0, 1] * !![1, r'; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uGL_zero : uGL (0 : K) = 1 := by
  apply Units.ext
  change !![1, 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def wGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_wGL : ((wGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem lSp_dGL_conj_qSp (t : Kˣ × Kˣ) (x y z : K) :
    lSp K (dGL t) * qSp x y z * (lSp K (dGL t))⁻¹ =
      qSp ((t.1 : K) ^ 2 * x) ((t.1 : K) * t.2 * y) ((t.2 : K) ^ 2 * z) := by
  rw [qSp, lSp_conj_qSpS]
  refine qSpS_congr ?_ _ _
  rw [coe_dGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem lSp_uGL_conj_qSp (r x y z : K) :
    lSp K (uGL r) * qSp x y z * (lSp K (uGL r))⁻¹ =
      qSp (x + 2 * r * y + r ^ 2 * z) (y + r * z) z := by
  rw [qSp, lSp_conj_qSpS]
  refine qSpS_congr ?_ _ _
  rw [coe_uGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm3, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem lSp_wGL_conj_qSp (x y z : K) :
    lSp K wGL * qSp x y z * (lSp K wGL)⁻¹ = qSp z y x := by
  rw [qSp, lSp_conj_qSpS]
  refine qSpS_congr ?_ _ _
  rw [coe_wGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symm3, Matrix.mul_apply, Fin.sum_univ_two]

theorem dGL_mul_uGL (t : Kˣ × Kˣ) (r : K) :
    dGL t * uGL r = uGL ((t.1 : K) * (t.2 : K)⁻¹ * r) * dGL t := by
  have h2 : (t.2 : K) ≠ 0 := t.2.ne_zero
  apply Units.ext
  change diagonal ![(t.1 : K), (t.2 : K)] * !![1, r; 0, 1] =
    !![1, (t.1 : K) * (t.2 : K)⁻¹ * r; 0, 1] * diagonal ![(t.1 : K), (t.2 : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

@[expose] noncomputable def nSp (r : K) : StatedSp 2 K := lSp K (uGL r)

theorem nSp_add (r r' : K) : nSp (r + r') = nSp r * nSp r' := by
  rw [nSp, nSp, nSp, uGL_add, map_mul]

theorem nSp_zero : nSp (0 : K) = 1 := by
  rw [nSp, uGL_zero, map_one]

theorem nSp_inv (r : K) : (nSp r)⁻¹ = nSp (-r) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [← nSp_add, add_neg_cancel, nSp_zero]

theorem lSp_dGL_conj_nSp (t : Kˣ × Kˣ) (r : K) :
    lSp K (dGL t) * nSp r * (lSp K (dGL t))⁻¹ = nSp ((t.1 : K) * (t.2 : K)⁻¹ * r) := by
  rw [nSp, nSp, ← map_mul, dGL_mul_uGL, map_mul, mul_inv_cancel_right]

theorem nSp_conj_qSp (r x y z : K) :
    nSp r * qSp x y z * (nSp r)⁻¹ = qSp (x + 2 * r * y + r ^ 2 * z) (y + r * z) z :=
  lSp_uGL_conj_qSp r x y z

end Matrices

section Subgroups

variable (K : Type) [Field K]

@[expose] def Qsp : Subgroup (StatedSp 2 K) where
  carrier := {g | ∃ x y z : K, g = qSp x y z}
  one_mem' := ⟨0, 0, 0, qSp_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, z, rfl⟩ ⟨x', y', z', rfl⟩
    exact ⟨_, _, _, qSp_mul x y z x' y' z'⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, rfl⟩
    exact ⟨_, _, _, qSp_inv x y z⟩

@[expose] noncomputable def Nsp : Subgroup (StatedSp 2 K) where
  carrier := {g | ∃ r : K, g = nSp r}
  one_mem' := ⟨0, nSp_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', (nSp_add r r').symm⟩
  inv_mem' := by
    rintro _ ⟨r, rfl⟩
    exact ⟨-r, nSp_inv r⟩

@[expose] noncomputable def Usp : Subgroup (StatedSp 2 K) where
  carrier := {g | ∃ x y z r : K, g = qSp x y z * nSp r}
  one_mem' := ⟨0, 0, 0, 0, by rw [qSp_zero, nSp_zero, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, z, r, rfl⟩ ⟨x', y', z', r', rfl⟩
    refine ⟨x + (x' + 2 * r * y' + r ^ 2 * z'), y + (y' + r * z'), z + z', r + r', ?_⟩
    rw [← qSp_mul, ← nSp_conj_qSp, nSp_add]
    group
  inv_mem' := by
    rintro _ ⟨x, y, z, r, rfl⟩
    refine ⟨-x + 2 * -r * -y + (-r) ^ 2 * -z, -y + -r * -z, -z, -r, ?_⟩
    rw [_root_.mul_inv_rev, nSp_inv, qSp_inv, ← nSp_conj_qSp]
    group

variable {K}

theorem eq_zero_of_nSp_eq_qSp {s a b c : K} (h : nSp s = qSp a b c) : s = 0 := by
  have h' := congrArg (fun g : StatedSp 2 K => mat 2 K g (Sum.inl 0) (Sum.inl 1)) h
  simp only [nSp, mat_lSp, mat_qSp, qMat, fromBlocks_apply₁₁, coe_uGL] at h'
  simpa using h'

theorem usp_injective {x y z r x' y' z' r' : K}
    (h : qSp x y z * nSp r = qSp x' y' z' * nSp r') : x = x' ∧ y = y' ∧ z = z' ∧ r = r' := by
  have h1 : nSp (r' + -r) = qSp (-x' + x) (-y' + y) (-z' + z) := by
    have : nSp r' * (nSp r)⁻¹ = (qSp x' y' z')⁻¹ * qSp x y z := by
      calc nSp r' * (nSp r)⁻¹ = (qSp x' y' z')⁻¹ * (qSp x' y' z' * nSp r') * (nSp r)⁻¹ := by group
        _ = (qSp x' y' z')⁻¹ * (qSp x y z * nSp r) * (nSp r)⁻¹ := by rw [h]
        _ = _ := by group
    rw [nSp_add, ← nSp_inv, this, qSp_inv, qSp_mul]
  have hr : r' + -r = 0 := eq_zero_of_nSp_eq_qSp h1
  have hr' : r = r' := by linear_combination -hr
  subst hr'
  obtain ⟨h2, h3, h4⟩ := qSp_injective (mul_right_cancel h)
  exact ⟨h2, h3, h4, rfl⟩

theorem card_Usp [Finite K] : Nat.card (Usp K) = Nat.card K ^ 4 := by
  let f : K × K × K × K → Usp K := fun v => ⟨qSp v.1 v.2.1 v.2.2.1 * nSp v.2.2.2, _, _, _, _, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := usp_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
    · obtain ⟨g, x, y, z, r, rfl⟩ := g
      exact ⟨(x, y, z, r), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

theorem card_sp_four [Finite K] :
    Nat.card (StatedSp 2 K) = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K

theorem isPGroup_Usp [Finite K] {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f) :
    IsPGroup p (Usp K) := by
  apply IsPGroup.of_card (n := 4 * f)
  rw [card_Usp, hK, ← pow_mul, mul_comm]

theorem not_dvd_index_Usp [Finite K] {p f : ℕ} [hp : Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) : ¬ p ∣ (Usp K).index := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : (Usp K).index = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) := by
    have h := (Usp K).card_mul_index
    rw [card_Usp, card_sp_four] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 4) h
  have hpq : p ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self p (by omega)
  have hp' := hp.out
  rw [h1]
  intro h
  rcases (Nat.Prime.dvd_mul hp').1 h with h2 | h2
  · have h3 : p ∣ Nat.card K ^ 2 := dvd_pow hpq (by omega)
    have := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  · have h3 : p ∣ Nat.card K ^ 4 := dvd_pow hpq (by omega)
    have := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)

end Subgroups

end CFSG.ClassicalInvolution.ModelFacts.OddCover
