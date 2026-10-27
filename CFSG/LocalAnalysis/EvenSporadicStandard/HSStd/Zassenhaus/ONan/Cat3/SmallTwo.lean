module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Open CFSG.Open.StatedAPI

private def Xz : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

private lemma xz_sq : Xz ^ 2 + Xz + 1 = 0 := by decide

private lemma xz_cube : Xz ^ 3 = 1 := by decide

private lemma xz_ne : Xz ≠ 1 := by decide

private def Cz : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private lemma cz_seven : Cz ^ 7 = 1 := by decide

private lemma cz_ne : Cz ≠ 1 := by decide

private lemma pow_six_of_isUnit {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A) : A ^ 6 = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := Nat.card_eq_fintype_card.symm.trans hK
  have hcardGL : Nat.card (GL (Fin 2) K) = 6 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hcardK]
    norm_num
  have h1 : (hA.unit : GL (Fin 2) K) ^ 6 = 1 := by
    have h := pow_card_eq_one' (x := hA.unit)
    rwa [hcardGL] at h
  calc A ^ 6 = ((hA.unit : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 6 := by
        rw [hA.unit_spec]
    _ = ((hA.unit ^ 6 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [Units.val_pow_eq_pow_val]
    _ = 1 := by rw [h1, Units.val_one]

private lemma pow_six_of_commute_blk {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2)
    [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) (hX : X ^ 2 + X + 1 = 0)
    (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (hN : IsUnit N)
    (hcomm : N * Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 2) (Fin 2) K) =
      Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 2) (Fin 2) K) * N) :
    N ^ 6 = 1 := by
  let A := N.toBlocks₁₁
  let B := N.toBlocks₁₂
  let C := N.toBlocks₂₁
  let D := N.toBlocks₂₂
  have hN_eq : N = Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks N).symm
  have hB : B = X * B := by
    have h1 := congrArg Matrix.toBlocks₁₂ hcomm
    rw [hN_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₂] at h1
    simpa using h1
  have hC : C * X = C := by
    have h1 := congrArg Matrix.toBlocks₂₁ hcomm
    rw [hN_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₁] at h1
    simpa using h1
  have hB2 : X ^ 2 * B = B := by rw [pow_two, Matrix.mul_assoc, ← hB, ← hB]
  have hB0 : B = 0 := by
    have h3 : B + B + B = 0 := by
      calc B + B + B = X ^ 2 * B + X * B + 1 * B := by rw [hB2, ← hB, Matrix.one_mul]
        _ = (X ^ 2 + X + 1) * B := by rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
        _ = 0 := by rw [hX, Matrix.zero_mul]
    rwa [CharTwo.add_self_eq_zero, zero_add] at h3
  have hC2 : C * X ^ 2 = C := by rw [pow_two, ← Matrix.mul_assoc, hC, hC]
  have hC0 : C = 0 := by
    have h3 : C + C + C = 0 := by
      calc C + C + C = C * X ^ 2 + C * X + C * 1 := by rw [hC2, hC, Matrix.mul_one]
        _ = C * (X ^ 2 + X + 1) := by rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
        _ = 0 := by rw [hX, Matrix.mul_zero]
    rwa [CharTwo.add_self_eq_zero, zero_add] at h3
  have hNdiag : N = Matrix.fromBlocks A 0 0 D := by rw [hN_eq, hB0, hC0]
  have hAD : IsUnit A ∧ IsUnit D := by
    have h := hN
    rw [hNdiag, Matrix.isUnit_fromBlocks_zero₂₁] at h
    exact h
  obtain ⟨hA, hD⟩ := hAD
  have hA6 : A ^ 6 = 1 := pow_six_of_isUnit hK hA
  have hD6 : D ^ 6 = 1 := pow_six_of_isUnit hK hD
  rw [hNdiag, Matrix.fromBlocks_diagonal_pow, hA6, hD6, Matrix.fromBlocks_one]

private noncomputable def glSumEquivStatedProjSL (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) {m n N : ℕ} (e : Fin m ⊕ Fin n ≃ Fin N) :
    GL (Fin m ⊕ Fin n) K ≃* StatedProj (StatedSL N K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have htop : StatedSL N K = ⊤ := statedSL_eq_top_of_card_two hK N
  have hbot : (StatedScalars (Fin N) K).subgroupOf (StatedSL N K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK (Fin N), Subgroup.bot_subgroupOf]
  let e1 : GL (Fin m ⊕ Fin n) K ≃* GL (Fin N) K :=
    Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv
  let e2 : GL (Fin N) K ≃* StatedSL N K :=
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm
  let e3 : StatedSL N K ≃* StatedProj (StatedSL N K) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
  exact e1.trans (e2.trans e3)

theorem false_of_psl_four_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hC : CentHyp (StatedProj (StatedSL 4 K))) : False := by
  have hC' : CentHyp (GL (Fin 2 ⊕ Fin 2) K) :=
    CentHyp.of_mulEquiv
      (glSumEquivStatedProjSL K hK (N := 4) (finSumFinEquiv (m := 2) (n := 2))) hC
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := Nat.card_eq_fintype_card.symm.trans hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime hcardK
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hf_inj : Function.Injective f := ZMod.castHom_injective K
  let X : Matrix (Fin 2) (Fin 2) K := (RingHom.mapMatrix f) Xz
  have hX : X ^ 2 + X + 1 = 0 := by
    have h := congrArg (RingHom.mapMatrix f) xz_sq
    simpa [X, map_add, map_pow, map_one, map_zero] using h
  have hX3 : X ^ 3 = 1 := by
    have h := congrArg (RingHom.mapMatrix f) xz_cube
    simpa [X, map_pow, map_one] using h
  have hXne : X ≠ 1 := by
    intro h
    apply xz_ne
    have h1 : Xz.map f = 1 := by
      simpa [X, RingHom.mapMatrix_apply] using h
    apply Matrix.map_injective hf_inj
    dsimp only
    rw [Matrix.map_one (⇑f) (map_zero f) (map_one f)]
    exact h1
  let M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := Matrix.fromBlocks X 0 0 1
  have hM3 : M ^ 3 = 1 := by
    dsimp only [M]
    rw [Matrix.fromBlocks_diagonal_pow, hX3, one_pow, Matrix.fromBlocks_one]
  have hMne : M ≠ 1 := by
    intro h
    apply hXne
    have h1 := congrArg Matrix.toBlocks₁₁ h
    rw [Matrix.toBlocks_fromBlocks₁₁,
      show (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Matrix.fromBlocks 1 0 0 1
        from Matrix.fromBlocks_one.symm,
      Matrix.toBlocks_fromBlocks₁₁] at h1
    exact h1
  have hM_mul : M * M ^ 2 = 1 := by rw [← pow_succ']; exact hM3
  have hM_mul' : M ^ 2 * M = 1 := by rw [← pow_succ]; exact hM3
  let x : GL (Fin 2 ⊕ Fin 2) K := Units.mk M (M ^ 2) hM_mul hM_mul'
  have hx : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa [x] using hM3
    · intro h
      apply hMne
      have h1 := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
        (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
      simpa [x] using h1
  obtain ⟨y, hy5, hyx⟩ := hC'.exists_five hx
  have hyx_mat : (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M =
      M * (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have h1 := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hyx
    simpa [x, Units.val_mul] using h1
  have hNunit : IsUnit (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := ⟨y, rfl⟩
  have hy6mat : (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 6 = 1 :=
    pow_six_of_commute_blk hK X hX _ hNunit (by simpa [M] using hyx_mat)
  have hy6 : y ^ 6 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hy6mat
  have hdvd : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one hy6
  rw [hy5] at hdvd
  exact absurd hdvd (by norm_num)

theorem false_of_psl_five_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hC : CentHyp (StatedProj (StatedSL 5 K))) : False := by
  have hC' : CentHyp (GL (Fin 2 ⊕ Fin 3) K) :=
    CentHyp.of_mulEquiv
      (glSumEquivStatedProjSL K hK (N := 5) (finSumFinEquiv (m := 2) (n := 3))) hC
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := Nat.card_eq_fintype_card.symm.trans hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime hcardK
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hf_inj : Function.Injective f := ZMod.castHom_injective K
  let X : Matrix (Fin 2) (Fin 2) K := (RingHom.mapMatrix f) Xz
  have hX : X ^ 2 + X + 1 = 0 := by
    have h := congrArg (RingHom.mapMatrix f) xz_sq
    simpa [X, map_add, map_pow, map_one, map_zero] using h
  have hX3 : X ^ 3 = 1 := by
    have h := congrArg (RingHom.mapMatrix f) xz_cube
    simpa [X, map_pow, map_one] using h
  have hXne : X ≠ 1 := by
    intro h
    apply xz_ne
    have h1 : Xz.map f = 1 := by
      simpa [X, RingHom.mapMatrix_apply] using h
    apply Matrix.map_injective hf_inj
    dsimp only
    rw [Matrix.map_one (⇑f) (map_zero f) (map_one f)]
    exact h1
  let C : Matrix (Fin 3) (Fin 3) K := (RingHom.mapMatrix f) Cz
  have hC7 : C ^ 7 = 1 := by
    have h := congrArg (RingHom.mapMatrix f) cz_seven
    simpa [C, map_pow, map_one] using h
  have hCne : C ≠ 1 := by
    intro h
    apply cz_ne
    have h1 : Cz.map f = 1 := by
      simpa [C, RingHom.mapMatrix_apply] using h
    apply Matrix.map_injective hf_inj
    dsimp only
    rw [Matrix.map_one (⇑f) (map_zero f) (map_one f)]
    exact h1
  have hMN : Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 3) (Fin 3) K) *
        Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 C =
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 C *
        Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  let M : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K :=
    Matrix.fromBlocks X 0 0 (1 : Matrix (Fin 3) (Fin 3) K)
  let N : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K :=
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 C
  have hM3 : M ^ 3 = 1 := by
    dsimp only [M]
    rw [Matrix.fromBlocks_diagonal_pow, hX3, one_pow, Matrix.fromBlocks_one]
  have hN7 : N ^ 7 = 1 := by
    dsimp only [N]
    rw [Matrix.fromBlocks_diagonal_pow, one_pow, hC7, Matrix.fromBlocks_one]
  have hMne : M ≠ 1 := by
    intro h
    apply hXne
    have h1 := congrArg Matrix.toBlocks₁₁ h
    rw [Matrix.toBlocks_fromBlocks₁₁,
      show (1 : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K) = Matrix.fromBlocks 1 0 0 1
        from Matrix.fromBlocks_one.symm,
      Matrix.toBlocks_fromBlocks₁₁] at h1
    exact h1
  have hNne : N ≠ 1 := by
    intro h
    apply hCne
    have h1 := congrArg Matrix.toBlocks₂₂ h
    rw [Matrix.toBlocks_fromBlocks₂₂,
      show (1 : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K) = Matrix.fromBlocks 1 0 0 1
        from Matrix.fromBlocks_one.symm,
      Matrix.toBlocks_fromBlocks₂₂] at h1
    exact h1
  have hM_mul : M * M ^ 2 = 1 := by rw [← pow_succ']; exact hM3
  have hM_mul' : M ^ 2 * M = 1 := by rw [← pow_succ]; exact hM3
  let x : GL (Fin 2 ⊕ Fin 3) K := Units.mk M (M ^ 2) hM_mul hM_mul'
  have hx : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa [x] using hM3
    · intro h
      apply hMne
      have h1 := congrArg (fun u : GL (Fin 2 ⊕ Fin 3) K =>
        (u : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K)) h
      simpa [x] using h1
  have hN_mul : N * N ^ 6 = 1 := by rw [← pow_succ']; exact hN7
  have hN_mul' : N ^ 6 * N = 1 := by rw [← pow_succ]; exact hN7
  let y : GL (Fin 2 ⊕ Fin 3) K := Units.mk N (N ^ 6) hN_mul hN_mul'
  have hy : orderOf y = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa [y] using hN7
    · intro h
      apply hNne
      have h1 := congrArg (fun u : GL (Fin 2 ⊕ Fin 3) K =>
        (u : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) K)) h
      simpa [y] using h1
  have hyx : y * x = x * y := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    simpa [x, y, M, N] using hMN.symm
  have hmem := hC'.orderOf_mem hx hyx
  rw [hy] at hmem
  exact absurd hmem (by decide)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
