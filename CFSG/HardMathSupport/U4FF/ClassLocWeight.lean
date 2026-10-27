module

public import CFSG.HardMathSupport.U4FF.ClassKronRect
public import CFSG.HardMathSupport.U4FF.ClassLocSound

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups

section Diag

variable {k : Type*} [Field k]

theorem compound2_diagonal (d : Fin 4 → k) :
    compound2 (diagonal d) = diagonal (fun I : Fin 6 => d (pair6 I).1 * d (pair6 I).2) := by
  ext I J
  fin_cases I <;> fin_cases J <;> simp [compound2, pair6, diagonal_apply]

@[expose] def diagFac (d : Fin 4 → k) : (K : FK) → Fin K.dim → k
  | .N => fun i => d i
  | .W => fun I => d (pair6 I).1 * d (pair6 I).2
  | .S => fun i => (d i)⁻¹

theorem repK_diag (D : SL(4, k)) (d : Fin 4 → k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = diagonal d) (K : FK) :
    repK k K D = diagonal (diagFac d K) := by
  have hdet : ∏ i, d i = 1 := by
    have := D.det_coe
    rwa [hD, det_diagonal] at this
  cases K with
  | N => exact hD
  | W =>
    show compound2 (D : Matrix (Fin 4) (Fin 4) k) = _
    rw [hD]
    exact compound2_diagonal d
  | S =>
    show ((D⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)ᵀ = _
    rw [Matrix.SpecialLinearGroup.coe_inv, hD, adjugate_diagonal, diagonal_transpose]
    congr 1
    funext i
    have hi : d i ≠ 0 := by
      intro h0
      have : ∏ j, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
      rw [hdet] at this
      exact one_ne_zero this
    exact eq_inv_of_mul_eq_one_left (by
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      exact hdet)

theorem ambRepF_diag (fs : List FK) (D : SL(4, k)) (d : Fin 4 → k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = diagonal d) :
    ambRepF k fs D = diagonal (fun y => ∏ f : Fin fs.length,
      diagFac d (fs.get f) (((ambEq fs).symm y) f)) := by
  rw [ambRepF_apply, ambRep_apply]
  have h : (fun f : Fin fs.length => repK k (fs.get f) D) =
      fun f => diagonal (diagFac d (fs.get f)) := funext fun f => repK_diag D d hD _
  rw [h, kronDep_diagonal, submatrix_diagonal_equiv]
  rfl

@[expose] def hwFac (d : Fin 4 → k) (K : FK) : k := diagFac d K ⟨hwOf K, hwOf_lt K⟩

theorem hwVec_eq_single (fs : List FK) (k : Type*) [Field k] [CharP k 2] :
    (fun x => f2 k (hwVec fs x)) = Pi.single (ambEq fs (hwIdx fs)) 1 := by
  funext x
  have h1 : hwVec fs x = if x = ambEq fs (hwIdx fs) then 1 else 0 := by
    unfold hwVec
    have : (1 <<< hwEnc fs) = 0 ||| (1 <<< hwEnc fs) := by simp
    rw [this, bitF_or_shift]
    by_cases hx : x = ambEq fs (hwIdx fs)
    · simp [hx, hwEnc]
    · have : (x : ℕ) ≠ hwEnc fs := fun h => hx (Fin.ext h)
      simp [this, hx, bitF_zero]
  rw [h1, Pi.single_apply]
  by_cases hx : x = ambEq fs (hwIdx fs) <;> simp [hx]

variable [CharP k 2]

theorem ambRepF_diag_hw (fs : List FK) (D : SL(4, k)) (d : Fin 4 → k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k) = diagonal d) :
    ambRepF k fs D *ᵥ (fun x => f2 k (hwVec fs x)) =
      (∏ f : Fin fs.length, hwFac d (fs.get f)) • (fun x => f2 k (hwVec fs x)) := by
  rw [ambRepF_diag fs D d hD, hwVec_eq_single, diagonal_mulVec_single]
  have : (∏ f : Fin fs.length, diagFac d (fs.get f)
      (((ambEq fs).symm (ambEq fs (hwIdx fs))) f)) = ∏ f : Fin fs.length, hwFac d (fs.get f) := by
    simp [hwIdx, hwFac]
  rw [this, mul_one]
  ext x
  by_cases hx : x = ambEq fs (hwIdx fs) <;> simp [Pi.single_apply, hx]

theorem hwFac_N (d : Fin 4 → k) : hwFac d FK.N = d 0 := rfl

theorem hwFac_W (d : Fin 4 → k) : hwFac d FK.W = d 0 * d 1 := rfl

theorem hwFac_S (d : Fin 4 → k) : hwFac d FK.S = (d 3)⁻¹ := rfl

@[expose] def wtLoc (a b c : Bool) (d : Fin 4 → k) : k :=
  (if a then d 0 else 1) * (if b then d 0 * d 1 else 1) * (if c then d 0 * d 1 * d 2 else 1)

theorem prod_hwFac (a b c : Bool) (d : Fin 4 → k) (hdet : ∏ i, d i = 1) :
    (∏ f : Fin (fsOf a b c).length, hwFac d ((fsOf a b c).get f)) = wtLoc a b c d := by
  have h3 : (d 3)⁻¹ = d 0 * d 1 * d 2 := by
    rw [Fin.prod_univ_four] at hdet
    rw [inv_eq_of_mul_eq_one_right]
    linear_combination hdet
  simp only [List.get_eq_getElem, Fin.prod_univ_fun_getElem]
  cases a <;> cases b <;> cases c <;>
    simp [fsOf, wtLoc, hwFac_N, hwFac_W, hwFac_S, h3] <;> ring

end Diag

end CFSG.HardMathSupport.U4FF
