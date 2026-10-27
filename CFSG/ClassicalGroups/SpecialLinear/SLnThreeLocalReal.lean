module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSignedPerm

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open CFSG.ClassicalGroups.ThreeLocalSignedPerm

variable {K : Type} [Field K] {n : ℕ}

private def inverterMat (K : Type) [Field K] (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, b; b - a, -a]

private theorem inverterMat_mul_blockS (a b : K) :
    inverterMat K a b * blockS K = blockS K * blockS K * inverterMat K a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverterMat, blockS, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_inverterMat (a b : K) :
    (inverterMat K a b).det = -(a ^ 2 - a * b + b ^ 2) := by
  simp [inverterMat, Matrix.det_fin_two]
  ring

private theorem exists_inverter_coeffs [Finite K] (h3 : (3 : K) ≠ 0) :
    ∃ a b : K, a ^ 2 - a * b + b ^ 2 = -1 := by
  classical
  haveI := Fintype.ofFinite K
  by_cases h2 : ringChar K = 2
  · have h20 : (2 : K) = 0 := by
      have := (ringChar.spec K 2).mpr (by rw [h2])
      simpa using this
    exact ⟨1, 0, by linear_combination h20⟩
  · have hodd := FiniteField.odd_card_of_char_ne_two h2
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C 3 * Polynomial.X ^ 2)
      (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; rfl)
      (by rw [Polynomial.degree_C_mul_X_pow _ h3]; rfl) hodd
    refine ⟨x + y, 2 * y, ?_⟩
    simp at hxy
    linear_combination hxy

private theorem exists_inverterGL [Finite K] (h3 : (3 : K) ≠ 0) :
    ∃ T : GL (Fin 2) K, (T : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      T * blockSGL K = blockSGL K ^ 2 * T := by
  obtain ⟨a, b, hab⟩ := exists_inverter_coeffs (K := K) h3
  have hdet : (inverterMat K a b).det = 1 := by
    rw [det_inverterMat, hab]
    ring
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨inverterMat K a b, hdet⟩, hdet, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, pow_two]
  exact inverterMat_mul_blockS a b

private theorem inverter_mul_blockPowGL (T : GL (Fin 2) K)
    (hT : T * blockSGL K = blockSGL K ^ 2 * T) (k : ZMod 3) :
    T * blockPowGL K k = blockPowGL K (-k) * T := by
  have hp2 : blockPowGL K 2 = blockSGL K ^ 2 := by
    simp [blockPowGL, show (2 : ZMod 3).val = 2 from rfl]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [show (-0 : ZMod 3) = 0 by decide, blockPowGL_zero, mul_one, one_mul]
  rcases zmod_three_eq_one_or_two hk with rfl | rfl
  · rw [show (-1 : ZMod 3) = 2 by decide, hp2, blockPowGL_one]
    exact hT
  · rw [show (-2 : ZMod 3) = 1 by decide, blockPowGL_one, hp2]
    calc T * blockSGL K ^ 2 = (T * blockSGL K) * blockSGL K := by rw [pow_two, ← mul_assoc]
      _ = (blockSGL K ^ 2 * T) * blockSGL K := by rw [hT]
      _ = blockSGL K ^ 2 * (T * blockSGL K) := mul_assoc _ _ _
      _ = blockSGL K ^ 2 * (blockSGL K ^ 2 * T) := by rw [hT]
      _ = (blockSGL K ^ 2 * blockSGL K ^ 2) * T := (mul_assoc _ _ _).symm
      _ = blockSGL K * T := by
        rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, blockSGL_pow_three, one_mul,
          pow_one]

private theorem realizes_c₀_iff (hn : n = 6 ∨ n = 7) (g : StatedSL n K)
    (α : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)) :
    Realizes (c₀ K hn) g α ↔ ∀ v : Multiplicative (Fin 3 → ZMod 3),
      (g : GL (Fin n) K) * blkGL hn (fun i => blockPowGL K (Multiplicative.toAdd v i)) =
        blkGL hn (fun i => blockPowGL K (α (Multiplicative.toAdd v) i)) * g := by
  refine forall_congr' fun v => ?_
  rw [Subtype.ext_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_eq_iff_eq_mul]
  rfl

private theorem exists_realizes_neg [Finite K] (h3 : (3 : K) ≠ 0) (hn : n = 6 ∨ n = 7)
    (j : Fin 3) :
    ∃ g : StatedSL n K,
      Realizes (c₀ K hn) g fun v i => if i = j then -v i else v i := by
  classical
  obtain ⟨T, hdet, hT⟩ := exists_inverterGL (K := K) h3
  have hmem : blkGL hn (Function.update (1 : Fin 3 → GL (Fin 2) K) j T) ∈ StatedSL n K := by
    apply blkGL_mem_statedSL
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      simpa using hdet
    · simp [Function.update_of_ne hij]
  refine ⟨⟨_, hmem⟩, (realizes_c₀_iff hn _ _).mpr fun v => ?_⟩
  show blkGL hn _ * blkGL hn _ = blkGL hn _ * blkGL hn _
  simp only [← map_mul]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij
    simpa using inverter_mul_blockPowGL T hT (Multiplicative.toAdd v i)
  · simp [Function.update_of_ne hij, hij]

private def blkPerm (σ : Equiv.Perm (Fin 3)) : Equiv.Perm Blk :=
  Equiv.prodCongrRight fun _ => σ⁻¹

private def permGL (K : Type) [Field K] (σ : Equiv.Perm (Fin 3)) : GL Blk K :=
  MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Blk) (R := K)) (blkPerm σ)

private theorem coe_permGL (σ : Equiv.Perm (Fin 3)) :
    ((permGL K σ : GL Blk K) : Matrix Blk Blk K) = ((blkPerm σ)⁻¹).permMatrix K := rfl

private theorem det_permGL (σ : Equiv.Perm (Fin 3)) :
    ((permGL K σ : GL Blk K) : Matrix Blk Blk K).det = 1 := by
  rw [coe_permGL, Matrix.det_permutation]
  simp [blkPerm, Equiv.Perm.sign_prodCongrRight]

private theorem permGL_mul_blockDiagGL (σ : Equiv.Perm (Fin 3)) (M : Fin 3 → GL (Fin 2) K) :
    permGL K σ * blockDiagGL K M = blockDiagGL K (fun i => M (σ i)) * permGL K σ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_blockDiagGL, coe_blockDiagGL,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext ⟨p, i⟩ ⟨q, j⟩
  simp [blkPerm, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Equiv.Perm.inv_def,
    Equiv.eq_symm_apply]

private theorem exists_realizes_perm_c₀ (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin 3)) :
    ∃ g : StatedSL n K, Realizes (c₀ K hn) g fun v i => v (σ i) := by
  have hmem : embGL hn (permGL K σ) ∈ StatedSL n K := embGL_mem_statedSL hn _ (det_permGL σ)
  refine ⟨⟨_, hmem⟩, (realizes_c₀_iff hn _ _).mpr fun v => ?_⟩
  show embGL hn (permGL K σ) * (embGL hn).comp (blockDiagGL K) _ =
    (embGL hn).comp (blockDiagGL K) _ * embGL hn (permGL K σ)
  simp only [MonoidHom.comp_apply, ← map_mul]
  congr 1
  exact permGL_mul_blockDiagGL σ _

theorem exists_conj_c₀ [Finite K] (h3 : (3 : K) ≠ 0) (hn : n = 6 ∨ n = 7)
    (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    ∃ m : StatedSL n K, ∀ v : Multiplicative (Fin 3 → ZMod 3),
      m * c₀ K hn v * m⁻¹ =
        c₀ K hn (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) :=
  exists_conj_signedPerm (c := c₀ K hn)
    (fun x y _ => exists_realizes_perm_c₀ hn (Equiv.swap x y))
    (fun j => exists_realizes_neg h3 hn j) σ ε hε

theorem three_ne_zero_of_natCard_mod_three [Finite K] (h : Nat.card K % 3 = 2) :
    (3 : K) ≠ 0 := by
  intro h3
  haveI := Fintype.ofFinite K
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h3)
  have hne : ringChar K ≠ 1 := CharP.char_ne_one K (ringChar K)
  have hp : ringChar K = 3 := (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd).resolve_left hne
  haveI : CharP K 3 := hp ▸ ringChar.charP K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [Nat.card_eq_fintype_card, hm] at h
  have : 3 ∣ 3 ^ (m : ℕ) := dvd_pow_self 3 m.ne_zero
  omega

end CFSG.ClassicalGroups.SLnThreeLocal
