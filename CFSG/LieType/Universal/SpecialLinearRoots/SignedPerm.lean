module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

public section

namespace CFSG.LieType.Universal.SpecialLinear

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

@[expose] def signedPerm (π : Equiv.Perm ι) (ε : ι → R) : Matrix ι ι R :=
  of fun r s => if r = π s then ε s else 0

omit [Fintype ι] in
theorem signedPerm_apply (π : Equiv.Perm ι) (ε : ι → R) (r s : ι) :
    signedPerm π ε r s = if r = π s then ε s else 0 := rfl

theorem signedPerm_mul_signedPerm (π π' : Equiv.Perm ι) (ε ε' : ι → R) :
    signedPerm π ε * signedPerm π' ε' = signedPerm (π * π') fun s => ε (π' s) * ε' s := by
  ext r s
  rw [mul_apply, Finset.sum_eq_single (π' s) (fun t _ ht => by simp [signedPerm_apply, ht])
    (by simp)]
  by_cases h : r = π (π' s) <;> simp [signedPerm_apply, h]

omit [Fintype ι] in
theorem signedPerm_one (ε : ι → R) : signedPerm 1 ε = diagonal ε := by
  ext r s
  by_cases h : r = s <;> simp [signedPerm_apply, h]

theorem signedPerm_mul_single (π : Equiv.Perm ι) (ε : ι → R) (i j : ι) (c : R) :
    signedPerm π ε * single i j c = single (π i) j (ε i * c) := by
  ext r s
  rw [mul_apply, Finset.sum_eq_single i (fun t _ ht => by simp [Ne.symm ht]) (by simp)]
  by_cases h : r = π i <;> by_cases h' : j = s <;> simp [signedPerm_apply, h, h', eq_comm]

theorem single_mul_signedPerm (π : Equiv.Perm ι) (ε : ι → R) (i j : ι) (c : R) :
    single i j c * signedPerm π ε = single i (π.symm j) (c * ε (π.symm j)) := by
  ext r s
  rw [mul_apply, Finset.sum_eq_single j (fun t _ ht => by simp [Ne.symm ht]) (by simp)]
  by_cases h : i = r <;> by_cases h' : s = π.symm j
  · subst h'
    simp [signedPerm_apply, h]
  · have : j ≠ π s := fun e => h' (by rw [e, Equiv.symm_apply_apply])
    simp [signedPerm_apply, h, this, Ne.symm h']
  · simp [signedPerm_apply, h]
  · simp [signedPerm_apply, h]

theorem signedPerm_mul_diagonal (π : Equiv.Perm ι) (ε : ι → R) (d : ι → R) :
    signedPerm π ε * diagonal d = diagonal (fun r => d (π.symm r)) * signedPerm π ε := by
  ext r s
  by_cases h : r = π s
  · subst h
    simp [mul_diagonal, diagonal_mul, signedPerm_apply, mul_comm]
  · simp [mul_diagonal, diagonal_mul, signedPerm_apply, h]

open SpecialLinearGroup

theorem conj_transvection_of_coe_eq_signedPerm {g : SpecialLinearGroup ι R} {π : Equiv.Perm ι}
    {ε : ι → R} (hg : (g : Matrix ι ι R) = signedPerm π ε) (hε : ∀ s, ε s * ε s = 1)
    {i j : ι} (hij : i ≠ j) (c : R) :
    g * transvection hij c * g⁻¹ = transvection (π.injective.ne hij) (ε i * ε j * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply coeMonoidHom_injective
  simp only [map_mul, coeMonoidHom_apply, transvection_coe, hg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, signedPerm_mul_single, single_mul_signedPerm,
    Equiv.symm_apply_apply]
  congr 2
  linear_combination (ε i * c) * (hε j).symm

theorem conj_transvection_of_coe_eq_diagonal {F : Type*} [Field F] {g : SpecialLinearGroup ι F}
    {d : ι → F} (hg : (g : Matrix ι ι F) = diagonal d) {i j : ι} (hij : i ≠ j) (c : F) :
    g * transvection hij c * g⁻¹ = transvection hij (d i * c * (d j)⁻¹) := by
  have hd : d j ≠ 0 := diagonal_neZero d (by rw [← hg]; exact g.2) j
  rw [mul_inv_eq_iff_eq_mul]
  apply coeMonoidHom_injective
  simp only [map_mul, coeMonoidHom_apply, transvection_coe, hg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext r s
  by_cases h : i = r ∧ j = s
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_diagonal, hd]
  · simp [diagonal_mul, mul_diagonal, h]

theorem conj_eq_of_coe_eq_signedPerm {g h h' : SpecialLinearGroup ι R} {π : Equiv.Perm ι}
    {ε d : ι → R} (hg : (g : Matrix ι ι R) = signedPerm π ε)
    (hh : (h : Matrix ι ι R) = diagonal d)
    (hh' : (h' : Matrix ι ι R) = diagonal fun r => d (π.symm r)) : g * h * g⁻¹ = h' := by
  rw [mul_inv_eq_iff_eq_mul]
  apply coeMonoidHom_injective
  simp only [map_mul, coeMonoidHom_apply, hg, hh, hh', signedPerm_mul_diagonal]

theorem conj_diag2nUnit_of_coe_eq_signedPerm {g : SpecialLinearGroup ι R} {π : Equiv.Perm ι}
    {ε : ι → R} (hg : (g : Matrix ι ι R) = signedPerm π ε) {i j i' j' : ι} (hij : i ≠ j)
    (hij' : i' ≠ j') (hi : π i = i') (hj : π j = j') (t : Rˣ) :
    g * diag2nUnit hij t * g⁻¹ = diag2nUnit hij' t := by
  subst hi hj
  refine conj_eq_of_coe_eq_signedPerm hg (diag2nUnit_coe hij t) ?_
  rw [diag2nUnit_coe]
  congr 1
  funext r
  simp only [Equiv.symm_apply_eq]

theorem diag2nUnit_mul_diag2nUnit {i j l : ι} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (t : Rˣ) : diag2nUnit hij t * diag2nUnit hjl t = diag2nUnit hil t := by
  apply coeMonoidHom_injective
  simp only [map_mul, coeMonoidHom_apply, diag2nUnit_coe, diagonal_mul_diagonal]
  congr 1
  funext r
  by_cases hri : r = i
  · subst hri
    simp [hij, hil]
  by_cases hrj : r = j
  · subst hrj
    simp [hri, hjl]
  by_cases hrl : r = l
  · subst hrl
    simp [hri, hrj]
  · simp [hri, hrj, hrl]

theorem diag2nUnit_symm {i j : ι} (hij : i ≠ j) (t : Rˣ) :
    diag2nUnit hij.symm t = diag2nUnit hij t⁻¹ := by
  apply coeMonoidHom_injective
  simp only [coeMonoidHom_apply, diag2nUnit_coe, inv_inv]
  congr 1
  funext r
  grind

theorem diag2nUnit_mem {S : Subgroup (SpecialLinearGroup ι R)} {i j : ι} (hij : i ≠ j)
    (h₁ : ∀ c, SpecialLinearGroup.transvection hij c ∈ S)
    (h₂ : ∀ c, SpecialLinearGroup.transvection hij.symm c ∈ S) (t : Rˣ) :
    diag2nUnit hij t ∈ S := by
  rw [diag2nUnit_decompose]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h₁ _) (h₂ _)) (h₁ _)) (h₁ _)) (h₂ _)) (h₁ _)

def weylSign (a : ι) : ι → R := fun s => if s = a then -1 else 1

omit [Fintype ι] in
theorem weylSign_mul_self (a s : ι) : weylSign (R := R) a s * weylSign a s = 1 := by
  unfold weylSign
  split_ifs <;> simp

@[expose] def weylMatrix (a b : ι) : Matrix ι ι R := signedPerm (Equiv.swap a b) (weylSign a)

theorem coe_transvection_mul_transvection_mul_transvection {a b : ι} (hab : a ≠ b) :
    ((transvection hab (1 : R) * transvection hab.symm (-1) * transvection hab 1 :
      SpecialLinearGroup ι R) : Matrix ι ι R) = weylMatrix a b := by
  rw [← coeMonoidHom_apply]
  simp only [map_mul, coeMonoidHom_apply, transvection_coe, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hab.symm]
  ext r s
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, weylMatrix, signedPerm_apply,
    weylSign, Equiv.swap_apply_def, Matrix.zero_apply]
  grind

theorem weylMatrix_mul_self {a b : ι} (hab : a ≠ b) :
    weylMatrix (R := R) a b * weylMatrix a b =
      diagonal fun r => if r = a then -1 else if r = b then -1 else 1 := by
  rw [weylMatrix, signedPerm_mul_signedPerm, Equiv.swap_mul_self, signedPerm_one]
  congr 1
  funext r
  by_cases hra : r = a
  · subst hra
    simp [weylSign, hab.symm]
  by_cases hrb : r = b
  · subst hrb
    simp [weylSign, hra]
  · simp [weylSign, hra, hrb, Equiv.swap_apply_of_ne_of_ne]

theorem weylMatrix_braid {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    weylMatrix (R := R) a b * (weylMatrix b c * weylMatrix a b) =
      weylMatrix b c * (weylMatrix a b * weylMatrix b c) := by
  simp only [weylMatrix, signedPerm_mul_signedPerm]
  ext r s
  simp only [signedPerm_apply, Equiv.Perm.mul_apply, weylSign, Equiv.swap_apply_def]
  grind

theorem weylMatrix_comm {a b c d : ι} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    weylMatrix (R := R) a b * weylMatrix c d = weylMatrix c d * weylMatrix a b := by
  simp only [weylMatrix, signedPerm_mul_signedPerm]
  ext r s
  simp only [signedPerm_apply, Equiv.Perm.mul_apply, weylSign, Equiv.swap_apply_def]
  grind

end CFSG.LieType.Universal.SpecialLinear
