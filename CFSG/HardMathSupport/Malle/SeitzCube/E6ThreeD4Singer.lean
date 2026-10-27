module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.SingerDiag
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeKernel

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open scoped MatrixGroups

@[expose] def singerShift (Ω : Type) [Field Ω] : Matrix (Fin 3) (Fin 3) Ω :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

section Main

variable {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]

omit [IsAlgClosed Ω] in
theorem singer_eigen_ne {ζ : Ωˣ} {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) {i j : Fin 3}
    (h : ζ ^ (q ^ (i : ℕ)) = ζ ^ (q ^ (j : ℕ))) : i = j := by
  rw [pow_eq_pow_iff_modEq, hζ] at h
  have h' : ((q ^ (i : ℕ) : ℕ) : ZMod p) = ((q ^ (j : ℕ) : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  push_cast at h'
  exact omega_pow_inj hp hp3 hq h'

omit [IsAlgClosed Ω] in
theorem frobenius_algebraMap {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K) (c : K) :
    Fr (algebraMap K Ω c) = algebraMap K Ω c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_singer_frobenius {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : SL(3, K)} (hg : orderOf g = p) :
    ∃ (ζ : Ωˣ) (Q D : SL(3, Ω)) (d : Fin 3 → Ωˣ), orderOf ζ = p ∧
      (D : Matrix (Fin 3) (Fin 3) Ω) = Matrix.diagonal
        ![(ζ : Ω), (ζ : Ω) ^ Nat.card K, (ζ : Ω) ^ (Nat.card K ^ 2)] ∧
      Matrix.SpecialLinearGroup.map (algebraMap K Ω) g = Q * D * Q⁻¹ ∧
      ((Q⁻¹ * Matrix.SpecialLinearGroup.map Fr Q : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
        Matrix.diagonal (fun i => (d i : Ω)) * singerShift Ω := by
  classical
  set q := Nat.card K with hqdef
  obtain ⟨l, hl, s, hlord, hconj⟩ := exists_sl3_conj_singerDiag (K := K) (r := r) hp hp3 hpr hpq hg
  obtain ⟨f⟩ : Nonempty (FiniteField.Extension K r 3 →ₐ[K] Ω) := ⟨IsAlgClosed.lift⟩
  have hfinj : Function.Injective f := f.toRingHom.injective
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one l
    rw [hlord, h0, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  have hlp : l ^ p = 1 := by rw [← hlord]; exact pow_orderOf_eq_one l
  have hfl0 : f l ≠ 0 := fun h => hl0 (hfinj (by rw [h, map_zero]))
  set ζ : Ωˣ := Units.mk0 (f l) hfl0 with hζdef
  have hζord : orderOf ζ = p := by
    rw [← orderOf_units, Units.val_mk0, ← hlord]
    exact orderOf_injective f.toRingHom.toMonoidHom hfinj l
  set Q : SL(3, Ω) := Matrix.SpecialLinearGroup.map (f : FiniteField.Extension K r 3 →+* Ω) s
    with hQdef
  set D : SL(3, Ω) := Matrix.SpecialLinearGroup.map (f : FiniteField.Extension K r 3 →+* Ω)
    (singerDiag q l hl) with hDdef
  have hDc : (D : Matrix (Fin 3) (Fin 3) Ω) = Matrix.diagonal
      ![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] := by
    rw [hDdef, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, singerDiag, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [hζdef]
    · simp [hij]
  have hgQ : Matrix.SpecialLinearGroup.map (algebraMap K Ω) g = Q * D * Q⁻¹ := by
    have h1 := congrArg (Matrix.SpecialLinearGroup.map (f : FiniteField.Extension K r 3 →+* Ω))
      hconj
    rw [map_mul, map_mul, map_inv] at h1
    rw [← h1]
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have : Fintype K := Fintype.ofFinite K
  have hG : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map (algebraMap K Ω) g) =
      Matrix.SpecialLinearGroup.map (algebraMap K Ω) g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, frobenius_algebraMap hFr]
  have hq3 : (ζ : Ω) ^ (q ^ 3) = ζ := by
    have h3 : ((q : ZMod p)) ^ 3 = 1 := omega_cube hpq
    have h4 : ζ ^ (q ^ 3) = ζ ^ 1 := by
      rw [pow_eq_pow_iff_modEq, hζord]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by push_cast; simpa using h3)
    simpa using congrArg (fun u : Ωˣ => (u : Ω)) h4
  have hFD : ((Matrix.SpecialLinearGroup.map Fr D : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.diagonal ![(ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2), (ζ : Ω)] := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hDc]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · simp [hFr]
      · simp [hFr, ← pow_mul, pow_two]
      · have e : ((ζ : Ω) ^ (q ^ 2)) ^ q = ζ := by
          rw [← pow_mul]
          convert hq3 using 2
          ring
        simpa [hFr] using e
    · simp [hij]
  set G : SL(3, Ω) := Matrix.SpecialLinearGroup.map (algebraMap K Ω) g with hGdef
  set FQ : SL(3, Ω) := Matrix.SpecialLinearGroup.map Fr Q with hFQ
  set FD : SL(3, Ω) := Matrix.SpecialLinearGroup.map Fr D with hFDdef
  have h2 : G = FQ * FD * FQ⁻¹ := by
    calc G = Matrix.SpecialLinearGroup.map Fr G := hG.symm
      _ = FQ * FD * FQ⁻¹ := by
        rw [hgQ]
        simp only [map_mul, map_inv, hFQ, hFDdef]
  have hD : D = Q⁻¹ * G * Q := by rw [hgQ]; group
  have hM : (Q⁻¹ * FQ) * FD = D * (Q⁻¹ * FQ) := by
    have h3 : D * (Q⁻¹ * FQ) = Q⁻¹ * (G * FQ) := by rw [hD]; group
    have h4 : G * FQ = FQ * FD := by rw [h2]; group
    rw [h3, h4]; group
  have hMm : ((Q⁻¹ * FQ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) *
      Matrix.diagonal ![(ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2), (ζ : Ω)] =
      Matrix.diagonal ![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] *
        ((Q⁻¹ * FQ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) := by
    have := congrArg Subtype.val hM
    simp only [Matrix.SpecialLinearGroup.coe_mul, hFD, hDc] at this
    exact this
  set M : Matrix (Fin 3) (Fin 3) Ω := ((Q⁻¹ * FQ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω)
    with hMdef
  have hDk : ∀ k : Fin 3, (![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] k) =
      ((ζ ^ (q ^ (k : ℕ)) : Ωˣ) : Ω) := fun k => by
    fin_cases k <;> simp
  have hFk : ∀ j : Fin 3, (![(ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2), (ζ : Ω)] j) =
      ![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] (j + 1) := fun j => by
    fin_cases j <;> simp
  have hzero : ∀ i j : Fin 3, i ≠ j + 1 → M i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hMm i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hFk j] at h
    have hne : (![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] i) ≠
        ![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] (j + 1) := by
      rw [hDk i, hDk (j + 1)]
      intro h'
      exact hij (by
        have := singer_eigen_ne hp hp3 hζord hpq (Units.ext h')
        exact this)
    have : (![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] i -
        ![(ζ : Ω), (ζ : Ω) ^ q, (ζ : Ω) ^ (q ^ 2)] (j + 1)) * M i j = 0 := by
      linear_combination (-1 : Ω) * h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) hne
    · exact h0
  have hdet : M.det = 1 := Matrix.SpecialLinearGroup.det_coe (Q⁻¹ * FQ)
  have hd0 : ∀ i : Fin 3, M i (i - 1) ≠ 0 := by
    intro i hi
    apply one_ne_zero (α := Ω)
    rw [← hdet]
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    by_cases hj : j = i - 1
    · subst hj; exact hi
    · refine hzero i j fun h => hj ?_
      subst h
      simp
  refine ⟨ζ, Q, D, fun i => Units.mk0 (M i (i - 1)) (hd0 i), hζord, hDc, hgQ, ?_⟩
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Units.val_mk0, singerShift, Matrix.of_apply]
  by_cases hij : i = j + 1
  · subst hij
    simp
    rfl
  · rw [if_neg hij, mul_zero]
    exact hzero i j hij

end Main
end CFSG.HardMathSupport.Malle.SeitzCube
