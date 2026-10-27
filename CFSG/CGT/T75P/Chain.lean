module

public import CFSG.CGT.T75P.Split81

public section

namespace CFSG.CGT.T75P

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

structure TransvChain (n k : ℕ) where
  E : Fin k → SL(n, GaloisField 2 1)
  axis : Fin k → Fin n
  axis_inj : Function.Injective axis
  isTrans : ∀ i, IsTransvection (E i)
  fixed_of : ∀ i (v : Fin n → GaloisField 2 1), v (axis i) = 0 →
    (E i : Matrix (Fin n) (Fin n) (GaloisField 2 1)) *ᵥ v = v
  odd_index : Odd (Subgroup.closure (Set.range E)).index

noncomputable def zmodHom : ZMod 2 →+* GaloisField 2 1 := ZMod.castHom (dvd_refl 2) _

noncomputable def sl3a : SL(3, GaloisField 2 1) :=
  ⟨zmodHom.mapMatrix sZ1, by
    have := RingHom.map_det zmodHom sZ1
    rw [sZ1_det, map_one] at this
    exact this.symm⟩

noncomputable def sl3b : SL(3, GaloisField 2 1) :=
  ⟨zmodHom.mapMatrix sZ2, by
    have := RingHom.map_det zmodHom sZ2
    rw [sZ2_det, map_one] at this
    exact this.symm⟩

theorem sl3a_sq : sl3a * sl3a = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  show zmodHom.mapMatrix sZ1 * zmodHom.mapMatrix sZ1 = 1
  rw [← map_mul, sZ1_sq, map_one]

theorem sl3b_sq : sl3b * sl3b = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  show zmodHom.mapMatrix sZ2 * zmodHom.mapMatrix sZ2 = 1
  rw [← map_mul, sZ2_sq, map_one]

theorem sl3_pow (k : ℕ) : (((sl3a * sl3b) ^ k : SL(3, GaloisField 2 1)) :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) = zmodHom.mapMatrix ((sZ1 * sZ2) ^ k) := by
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, map_pow, map_mul]
  rfl

theorem sl3_pow4 : (sl3a * sl3b) ^ 4 = 1 := by
  apply Subtype.ext
  rw [sl3_pow, sZ12_pow4, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem sl3_pow2 : (sl3a * sl3b) ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg (fun m : SL(3, GaloisField 2 1) => (m : Matrix (Fin 3) (Fin 3) (GaloisField 2 1))) h
  simp only [sl3_pow, Matrix.SpecialLinearGroup.coe_one] at h'
  have hinj : Function.Injective (zmodHom.mapMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) →+*
      Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) := Matrix.map_injective zmodHom.injective
  exact sZ12_pow2 (hinj (by rw [h', map_one]))

theorem sl3a_apply (v : Fin 3 → GaloisField 2 1) :
    (sl3a : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) *ᵥ v = v + v 1 • Pi.single 0 1 := by
  funext i
  fin_cases i <;> simp [sl3a, zmodHom, sZ1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem sl3b_apply (v : Fin 3 → GaloisField 2 1) :
    (sl3b : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) *ᵥ v = v + v 2 • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [sl3b, zmodHom, sZ2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem sl3a_ne_one : sl3a ≠ 1 := by
  intro h
  have := congrArg (fun m : SL(3, GaloisField 2 1) => (m : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) 0 1) h
  simp [sl3a, zmodHom, sZ1] at this

theorem sl3b_ne_one : sl3b ≠ 1 := by
  intro h
  have := congrArg (fun m : SL(3, GaloisField 2 1) => (m : Matrix (Fin 3) (Fin 3) (GaloisField 2 1)) 1 2) h
  simp [sl3b, zmodHom, sZ2] at this

noncomputable def chain3 : TransvChain 3 2 where
  E := fun i => if i = 0 then sl3a else sl3b
  axis := fun i => if i = 0 then 1 else 2
  axis_inj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  isTrans := by
    intro i
    fin_cases i
    · exact isTransvection_of_apply sl3a (LinearMap.proj 1) (Pi.single 0 1) (by simp)
        sl3a_apply sl3a_ne_one
    · exact isTransvection_of_apply sl3b (LinearMap.proj 2) (Pi.single 1 1) (by simp)
        sl3b_apply sl3b_ne_one
  fixed_of := by
    intro i v hv
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ite_true] at hv ⊢
      rw [sl3a_apply, hv]
      simp
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false] at hv ⊢
      rw [sl3b_apply, hv]
      simp
  odd_index := by
    have hrange : Set.range (fun i : Fin 2 => if i = 0 then sl3a else sl3b) = {sl3a, sl3b} := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    rw [hrange]
    have h8 : Nat.card (Subgroup.closure ({sl3a, sl3b} : Set SL(3, GaloisField 2 1))) = 8 :=
      CFSG.CGT.Timmesfeld75.card_closure_pair_eq_eight sl3a_sq sl3b_sq sl3_pow4 sl3_pow2
    have h := Subgroup.index_mul_card (Subgroup.closure ({sl3a, sl3b} : Set SL(3, GaloisField 2 1)))
    rw [h8, card_SL_three_two] at h
    have : (Subgroup.closure ({sl3a, sl3b} : Set SL(3, GaloisField 2 1))).index = 21 := by omega
    rw [this]
    decide

end CFSG.CGT.T75P
