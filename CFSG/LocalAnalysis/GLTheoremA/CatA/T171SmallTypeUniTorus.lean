module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadRk

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Dickson.Sec6.I1431
open Matrix

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] def tEntry5 (w : Fin 5 → rootsOfUnity 3 K) (k : ℕ) : Kˣ :=
  if k = 0 then (w 0 : Kˣ) else if k = 1 then (w 1 : Kˣ) else if k = 2 then (w 2 : Kˣ)
    else if k = 3 then (w 3 : Kˣ) else if k = 4 then (w 4 : Kˣ)
    else if k = 5 then ∏ i, (w i : Kˣ) else if k = 6 then ∏ i, (w i : Kˣ) else 1

private theorem tEntry5_apply_zero (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 0 = (w 0 : Kˣ) := rfl

private theorem tEntry5_apply_one (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 1 = (w 1 : Kˣ) := rfl

private theorem tEntry5_apply_two (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 2 = (w 2 : Kˣ) := rfl

private theorem tEntry5_apply_three (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 3 = (w 3 : Kˣ) := rfl

private theorem tEntry5_apply_four (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 4 = (w 4 : Kˣ) := rfl

private theorem tEntry5_apply_five (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 5 = ∏ i, (w i : Kˣ) := rfl

private theorem tEntry5_apply_six (w : Fin 5 → rootsOfUnity 3 K) :
    tEntry5 w 6 = ∏ i, (w i : Kˣ) := rfl

private theorem tCube (w : Fin 5 → rootsOfUnity 3 K) (i : Fin 5) : (w i : Kˣ) ^ 3 = 1 :=
  (mem_rootsOfUnity 3 (w i : Kˣ)).1 (w i).2

private theorem tEntry5_mul (w w' : Fin 5 → rootsOfUnity 3 K) (k : ℕ) :
    tEntry5 (w * w') k = tEntry5 w k * tEntry5 w' k := by
  unfold tEntry5
  split_ifs <;> simp [Finset.prod_mul_distrib, mul_assoc]

private theorem tEntry5_one (k : ℕ) : tEntry5 (1 : Fin 5 → rootsOfUnity 3 K) k = 1 := by
  unfold tEntry5
  split_ifs <;> simp

private theorem prod_tEntry5 (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) :
    ∏ i : Fin n, tEntry5 w i = 1 := by
  have hu : (∏ i, (w i : Kˣ)) ^ 3 = 1 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => tCube w i
  have hP : (∏ i : Fin 5, (w i : Kˣ)) =
      (w 0 : Kˣ) * (w 1 : Kˣ) * (w 2 : Kˣ) * (w 3 : Kˣ) * (w 4 : Kˣ) :=
    Fin.prod_univ_five _
  have hkey : (∏ i, (w i : Kˣ)) * (∏ i, (w i : Kˣ)) * (∏ i, (w i : Kˣ)) = 1 := by
    rw [show (∏ i, (w i : Kˣ)) * (∏ i, (w i : Kˣ)) * (∏ i, (w i : Kˣ)) =
      (∏ i, (w i : Kˣ)) ^ 3 from by rw [pow_succ, pow_succ, pow_one]]
    exact hu
  rw [show (∏ i : Fin n, tEntry5 w i) = ∏ k ∈ Finset.range n, tEntry5 w k from
    Fin.prod_univ_eq_prod_range (fun k => tEntry5 w k) n,
    ← Finset.prod_subset (Finset.range_subset_range.2 hn) ?_]
  · rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_zero]
    simp only [tEntry5_apply_zero, tEntry5_apply_one, tEntry5_apply_two, tEntry5_apply_three,
      tEntry5_apply_four, tEntry5_apply_five, tEntry5_apply_six, one_mul]
    rw [← hP]
    exact hkey
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [tEntry5, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega,
      show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega, show k ≠ 6 by omega]

@[expose] noncomputable def tDiag5 (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) :
    SpecialLinearGroup (Fin n) K :=
  ⟨diagonal fun i : Fin n => (tEntry5 w i : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_tEntry5 hn w, Units.val_one]⟩

theorem coe_tDiag5 (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) :
    (tDiag5 hn w : Matrix (Fin n) (Fin n) K) = diagonal fun i : Fin n => (tEntry5 w i : K) :=
  rfl

private theorem tDiag5_apply (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) (i : Fin n) :
    (tDiag5 hn w : Matrix (Fin n) (Fin n) K) i i = (tEntry5 w i : K) := by
  rw [coe_tDiag5, diagonal_apply_eq]

theorem tDiag5_mul (hn : 7 ≤ n) (w w' : Fin 5 → rootsOfUnity 3 K) :
    tDiag5 hn (w * w') = tDiag5 hn w * tDiag5 hn w' := by
  have h : (tDiag5 hn (w * w') : Matrix (Fin n) (Fin n) K) =
      (tDiag5 hn w : Matrix (Fin n) (Fin n) K) * (tDiag5 hn w' : Matrix (Fin n) (Fin n) K) := by
    simp only [coe_tDiag5, diagonal_mul_diagonal, tEntry5_mul, Units.val_mul]
  exact Subtype.ext
    (h.trans (Matrix.SpecialLinearGroup.coe_mul (tDiag5 hn w) (tDiag5 hn w')).symm)

theorem tDiag5_one (hn : 7 ≤ n) : tDiag5 (K := K) hn 1 = 1 := by
  apply Subtype.ext
  simp only [coe_tDiag5, tEntry5_one, Units.val_one, SpecialLinearGroup.coe_one]
  exact diagonal_one

@[expose] noncomputable def torusHom5SU (hn : 7 ≤ n) :
    (Fin 5 → rootsOfUnity 3 K) →* SpecialLinearGroup (Fin n) K where
  toFun w := tDiag5 hn w
  map_one' := tDiag5_one hn
  map_mul' w w' := tDiag5_mul hn w w'

theorem pow_three_eq_one_five (w : Fin 5 → rootsOfUnity 3 K) : w ^ 3 = 1 := by
  funext i
  simpa using pow_three_eq_one_roots (w i)

private theorem tEntry5_mem_unitNorm1 (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1)
    (w : Fin 5 → rootsOfUnity 3 K) (k : ℕ) : tEntry5 w k ∈ unitNorm1 h := by
  have hu : (∏ i, (w i : Kˣ)) ^ 3 = 1 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => tCube w i
  unfold tEntry5
  split_ifs
  · exact mem_unitNorm1_of_cube h hdvd (tCube w 0)
  · exact mem_unitNorm1_of_cube h hdvd (tCube w 1)
  · exact mem_unitNorm1_of_cube h hdvd (tCube w 2)
  · exact mem_unitNorm1_of_cube h hdvd (tCube w 3)
  · exact mem_unitNorm1_of_cube h hdvd (tCube w 4)
  · exact mem_unitNorm1_of_cube h hdvd hu
  · exact mem_unitNorm1_of_cube h hdvd hu
  · exact one_mem _

theorem toGL_tDiag5_mem_gramSU (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1)
    (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) :
    (Matrix.SpecialLinearGroup.toGL (tDiag5 hn w) : GL (Fin n) K) ∈
      gramSU h (idGram K n) := by
  rw [mem_gramSU_iff_unitary, mem_primeFormUnitary]
  refine ⟨?_, (tDiag5 hn w).2⟩
  have hu : ∀ i : Fin n, h.bar (tEntry5 w i : K) * (tEntry5 w i : K) = 1 :=
    fun i => (mem_unitNorm1 h).1 (tEntry5_mem_unitNorm1 h hdvd w i)
  show ((diagonal fun i : Fin n => (tEntry5 w i : K)).map h.bar)ᵀ *
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      diagonal (fun i : Fin n => (tEntry5 w i : K)) =
    ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [Units.val_one, Matrix.mul_one, Matrix.diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal,
    show (fun i : Fin n => h.bar (tEntry5 w i : K) * (tEntry5 w i : K)) = fun _ => 1 from
      funext hu,
    diagonal_one]

@[expose] noncomputable def suTorus5 (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1)
    (hn : 7 ≤ n) : (Fin 5 → rootsOfUnity 3 K) →* gramSU h (idGram K n) :=
  ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).comp
    (torusHom5SU hn)).codRestrict (gramSU h (idGram K n)) fun w =>
      toGL_tDiag5_mem_gramSU h hdvd hn w

theorem tDiag5_scalar (hn : 7 ≤ n) {w : Fin 5 → rootsOfUnity 3 K}
    (h : tDiag5 hn w ∈ scalars n K) : w = 1 := by
  obtain ⟨z, -, hz⟩ := mem_scalars.1 h
  have hc : ∀ i : Fin n, (tEntry5 w i : K) = (z : K) := by
    intro i
    have happ := tDiag5_apply (K := K) hn w i
    rw [hz, scalar_apply, diagonal_apply_eq] at happ
    exact happ.symm
  have h0 : (w 0 : Kˣ) = z := Units.ext (by simpa [tEntry5] using hc ⟨0, by omega⟩)
  have h1 : (w 1 : Kˣ) = z := Units.ext (by simpa [tEntry5] using hc ⟨1, by omega⟩)
  have h2 : (w 2 : Kˣ) = z := Units.ext (by simpa [tEntry5] using hc ⟨2, by omega⟩)
  have h3 : (w 3 : Kˣ) = z := Units.ext (by simpa [tEntry5] using hc ⟨3, by omega⟩)
  have h4 : (w 4 : Kˣ) = z := Units.ext (by simpa [tEntry5] using hc ⟨4, by omega⟩)
  have h5 : (∏ i, (w i : Kˣ)) = z := Units.ext (by simpa [tEntry5] using hc ⟨5, by omega⟩)
  have hz3 : z ^ 3 = 1 := by
    rw [← h0]
    exact tCube w 0
  have hfun : ∀ i, (w i : Kˣ) = z := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hP : (∏ i, (w i : Kˣ)) = z ^ 5 := by
    rw [Finset.prod_congr rfl (fun i _ => hfun i), Finset.prod_const]
    simp
  have hz5 : z ^ 5 = z := by rw [← hP]; exact h5
  have hz2 : z ^ 2 = z := by
    calc z ^ 2 = 1 * z ^ 2 := (one_mul _).symm
      _ = z ^ 3 * z ^ 2 := by rw [hz3]
      _ = z ^ 5 := by rw [← pow_add]
      _ = z := hz5
  have hz1 : z = 1 := by
    have hh : z * z = z * 1 := by
      rw [mul_one, ← pow_two]
      exact hz2
    exact mul_left_cancel hh
  funext i
  fin_cases i
  · exact Subtype.ext (h0.trans hz1)
  · exact Subtype.ext (h1.trans hz1)
  · exact Subtype.ext (h2.trans hz1)
  · exact Subtype.ext (h3.trans hz1)
  · exact Subtype.ext (h4.trans hz1)

theorem suTorus5_normOne (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 7 ≤ n)
    {w : Fin 5 → rootsOfUnity 3 K}
    (hw : suTorus5 h hdvd hn w ∈ normOneScalars h (gramSU h (idGram K n)) n) : w = 1 := by
  obtain ⟨c, -, hcn, hc⟩ := hw
  refine tDiag5_scalar hn (mem_scalars.2 ⟨c, hcn, ?_⟩)
  have h1 : (tDiag5 hn w : Matrix (Fin n) (Fin n) K) =
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  rwa [GeneralLinearGroup.coe_scalar] at h1

theorem suTorus5_injective (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 7 ≤ n) :
    Function.Injective (suTorus5 h hdvd hn) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  exact suTorus5_normOne h hdvd hn (by rw [hw]; exact one_mem _)

theorem suTorus5_card (h : UnitaryFieldData ℓ f K) (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 7 ≤ n)
    (hroots : Nat.card (rootsOfUnity 3 K) = 3) :
    Nat.card (suTorus5 h hdvd hn).range = 3 ^ 5 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (suTorus5_injective h hdvd hn)).toEquiv,
    Nat.card_fun, Nat.card_fin, hroots]

theorem suTorus5_commute_swapSU [CharP K 2] (h : UnitaryFieldData ℓ f K)
    (hdvd : 3 ∣ ℓ ^ f + 1) (hn : 7 ≤ n) (w : Fin 5 → rootsOfUnity 3 K) :
    Commute (suTorus5 h hdvd hn w) (swapSU h hn) := by
  apply Subtype.ext
  apply Units.ext
  show (diagonal fun i : Fin n => ((tEntry5 w i : Kˣ) : K)) *
      ((swapGL (⟨5, by omega⟩ : Fin n) ⟨6, by omega⟩ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
    ((swapGL (⟨5, by omega⟩ : Fin n) ⟨6, by omega⟩ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *
      diagonal fun i : Fin n => ((tEntry5 w i : Kˣ) : K)
  rw [coe_swapGL]
  exact diagonal_commute_swap _ _ _ (by simp [tEntry5])

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
