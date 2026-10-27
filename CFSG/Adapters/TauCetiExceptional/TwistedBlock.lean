module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.TauCetiBridge.Twisted

variable {n m : ℕ}

section Block

variable (blk : Fin n → Fin m) (R : Type*) [CommRing R]

@[expose] def IsBlockDiag (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ a b, blk a ≠ blk b → M a b = 0

variable {blk R}

theorem IsBlockDiag.mul {M N : Matrix (Fin n) (Fin n) R} (hM : IsBlockDiag blk R M)
    (hN : IsBlockDiag blk R N) : IsBlockDiag blk R (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hak : blk a = blk k
  · rw [hN k b (hak ▸ hab), mul_zero]
  · rw [hM a k hak, zero_mul]

theorem isBlockDiag_one : IsBlockDiag blk R (1 : Matrix (Fin n) (Fin n) R) := fun _ _ hab =>
  Matrix.one_apply_ne fun h => hab (congrArg blk h)

variable (blk R) in
@[expose] def blockGL : Subgroup (Matrix.GeneralLinearGroup (Fin n) R) where
  carrier := {g | IsBlockDiag blk R (g : Matrix (Fin n) (Fin n) R) ∧
    IsBlockDiag blk R ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)}
  one_mem' := ⟨isBlockDiag_one, by rw [inv_one]; exact isBlockDiag_one⟩
  mul_mem' {g h} hg hh := ⟨by rw [Units.val_mul]; exact hg.1.mul hh.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hh.2.mul hg.2⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem mem_blockGL_of {g : Matrix.GeneralLinearGroup (Fin n) R}
    (h : IsBlockDiag blk R (g : Matrix (Fin n) (Fin n) R))
    (h' : IsBlockDiag blk R ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R)) : g ∈ blockGL blk R :=
  ⟨h, h'⟩

end Block

section Commutant

variable {L : Type*} [Field L]

theorem isDiag_of_commute_diagonal {r : ℕ} (h2 : (2 : L) ≠ 0) (wt : Fin n → Fin r → ℤ)
    (hwt : ∀ a i, wt a i = -1 ∨ wt a i = 0 ∨ wt a i = 1) (hinj : Function.Injective wt)
    {z : Matrix (Fin n) (Fin n) L}
    (hz : ∀ i, z * Matrix.diagonal (fun a => (wt a i : L)) =
      Matrix.diagonal (fun a => (wt a i : L)) * z) {a b : Fin n} (hab : a ≠ b) : z a b = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, wt a i ≠ wt b i := by
    by_contra h
    push Not at h
    exact hab (hinj (funext h))
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) L => M a b) (hz i)
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have hd : wt b i - wt a i = 1 ∨ wt b i - wt a i = -1 ∨ wt b i - wt a i = 2 ∨
      wt b i - wt a i = -2 := by
    rcases hwt a i with ha | ha | ha <;> rcases hwt b i with hb | hb | hb <;> omega
  have hne : (((wt b i - wt a i : ℤ)) : L) ≠ 0 := by
    rcases hd with h | h | h | h <;> rw [h] <;> push_cast
    · exact one_ne_zero
    · exact neg_ne_zero.2 one_ne_zero
    · exact h2
    · exact neg_ne_zero.2 h2
  have e' : z a b * (((wt b i - wt a i : ℤ)) : L) = 0 := by
    rw [Int.cast_sub, mul_sub, e, mul_comm (wt a i : L)]
    exact sub_self _
  exact (mul_eq_zero.1 e').resolve_right hne

theorem diag_eq_of_commute {z X : Matrix (Fin n) (Fin n) L}
    (hz : ∀ a b, a ≠ b → z a b = 0) (hX : z * X = X * z) {a b : Fin n} (hba : X b a ≠ 0) :
    z a a = z b b := by
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) L => M b a) hX
  simp only [Matrix.mul_apply] at e
  rw [Finset.sum_eq_single b (fun k _ hk => by rw [hz b k (Ne.symm hk), zero_mul])
      (by simp),
    Finset.sum_eq_single a (fun k _ hk => by rw [hz k a hk, mul_zero]) (by simp)] at e
  exact (mul_right_cancel₀ hba (e.trans (mul_comm _ _))).symm

theorem commute_of_diag (blk : Fin n → Fin m) {z w : Matrix (Fin n) (Fin n) L}
    (hz : ∀ a b, a ≠ b → z a b = 0) (hzb : ∀ a b, blk a = blk b → z a a = z b b)
    (hw : IsBlockDiag blk L w) : z * w = w * z := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single a (fun k _ hk => by rw [hz a k (Ne.symm hk), zero_mul]) (by simp),
    Finset.sum_eq_single b (fun k _ hk => by rw [hz k b hk, mul_zero]) (by simp)]
  by_cases hab : blk a = blk b
  · rw [hzb a b hab, mul_comm]
  · rw [hw a b hab, mul_zero, zero_mul]

end Commutant

end CFSG.TauCetiBridge.Twisted
