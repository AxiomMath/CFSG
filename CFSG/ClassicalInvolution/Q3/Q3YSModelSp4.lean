module

public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.ClassicalInvolution.Q3.Q3YSInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open Matrix CFSG.LieType.SteinbergBR.EvenSp CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic

section Planes

variable {K : Type} [Field K]

def swp : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

def swi : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

def sru : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem swp_mul_swp : (swp : Matrix.SpecialLinearGroup (Fin 2) K) * swp = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swp, Matrix.mul_apply, Fin.sum_univ_two]

theorem swi_mul_swi : (swi : Matrix.SpecialLinearGroup (Fin 2) K) * swi = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swi, Matrix.mul_apply, Fin.sum_univ_two]

theorem swp_mul_swi : (swp : Matrix.SpecialLinearGroup (Fin 2) K) * swi = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swp, swi, Matrix.mul_apply, Fin.sum_univ_two]

theorem swi_mul_swp : (swi : Matrix.SpecialLinearGroup (Fin 2) K) * swp = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swp, swi, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_mul_neg_one_sl2 : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) * (-1) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  simp

theorem sru_mul_swp_ne : (sru : Matrix.SpecialLinearGroup (Fin 2) K) * swp ≠ swp * sru := by
  intro h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [sru, swp, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem sru_mul_swi_ne : (sru : Matrix.SpecialLinearGroup (Fin 2) K) * swi ≠ swi * sru := by
  intro h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [sru, swi, Matrix.mul_apply, Fin.sum_univ_two] at h2

@[expose] noncomputable def spPlane (n : ℕ) :
    (Fin n → Matrix.SpecialLinearGroup (Fin 2) K) →* StatedSp n K :=
  MonoidHom.codRestrict
    ((planeHom (K := K) (n := n)).comp
      (MonoidHom.compLeft Matrix.SpecialLinearGroup.toGL (Fin n)))
    (StatedSp n K) (fun g => planeHom_mem_statedSp _ (fun j => by
      simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]))

theorem spPlane_val (n : ℕ) (g : Fin n → Matrix.SpecialLinearGroup (Fin 2) K) :
    (((spPlane n g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      planeMat fun j => (g j : Matrix (Fin 2) (Fin 2) K) := rfl

theorem spPlane_injective (n : ℕ) : Function.Injective (spPlane (K := K) n) := by
  intro g g' h
  have h1 : planeHom (fun j => Matrix.SpecialLinearGroup.toGL (g j)) =
      planeHom (fun j => Matrix.SpecialLinearGroup.toGL (g' j)) :=
    congrArg (fun x : StatedSp n K => (x : GL (Fin n ⊕ Fin n) K)) h
  have h2 := planeHom_injective h1
  funext j
  apply Subtype.ext
  have := congrFun h2 j
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using congrArg
    (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) this

theorem spPlane_neg_one_val (n : ℕ) :
    (((spPlane n (fun _ => (-1 : Matrix.SpecialLinearGroup (Fin 2) K)) : StatedSp n K) :
      GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = -1 := by
  rw [spPlane_val]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [planeMat, Matrix.one_apply, Matrix.diagonal_apply, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one] <;>
    try (split_ifs <;> simp)

theorem spPlane_neg_one_mem_center (n : ℕ) :
    spPlane n (fun _ => (-1 : Matrix.SpecialLinearGroup (Fin 2) K)) ∈
      Subgroup.center (StatedSp n K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, spPlane_neg_one_val, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, Matrix.one_mul]

def pswap : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem pswap_mul_self : (pswap : Matrix (Fin 2) (Fin 2) K) * pswap = 1 := by
  rw [pswap, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pswap_transpose : (pswap : Matrix (Fin 2) (Fin 2) K)ᵀ = pswap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pswap]

theorem fromBlocks_pswap_mul_self :
    Matrix.fromBlocks (pswap : Matrix (Fin 2) (Fin 2) K) 0 0 pswap *
      Matrix.fromBlocks (pswap : Matrix (Fin 2) (Fin 2) K) 0 0 pswap = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [pswap_mul_self, Matrix.fromBlocks_one]

noncomputable def planeSwap : StatedSp 2 K :=
  ⟨⟨Matrix.fromBlocks pswap 0 0 pswap, Matrix.fromBlocks pswap 0 0 pswap,
    fromBlocks_pswap_mul_self, fromBlocks_pswap_mul_self⟩, by
    rw [mem_statedSp_iff']
    simp [Matrix.fromBlocks_transpose, pswap_transpose, Matrix.fromBlocks_multiply,
      pswap_mul_self]⟩

end Planes

section Main

open Matrix


theorem sp4KleinQuat3 : Sp4KleinQuat3 := by
  show ∃ y y' : StatedSp 2 (GaloisField 3 1), KleinQuat (StatedSp 2 (GaloisField 3 1)) y y'
  have hyy : spPlane 2 (fun _ => (swp : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1))) *
      spPlane 2 (fun _ => swp) =
      spPlane 2 (fun _ => (-1 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1))) := by
    rw [← map_mul]
    congr 1
    funext j
    simp [Pi.mul_apply, swp_mul_swp]
  have hyy' : spPlane 2 (fun _ => (swp : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1))) *
      spPlane 2 ![swp, swi] =
      spPlane 2 ![(-1 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)), 1] := by
    rw [← map_mul]
    congr 1
    funext j
    fin_cases j <;> simp [Pi.mul_apply, swp_mul_swp, swp_mul_swi]
  refine ⟨spPlane 2 (fun _ => swp), spPlane 2 ![swp, swi], ?_⟩
  refine
    { comm := ?_
      sq_eq := ?_
      sq_central := ?_
      sq_sq := ?_
      not_central := ?_
      not_central' := ?_
      prod_not_central := ?_ }
  · rw [← map_mul, ← map_mul]
    congr 1
    funext j
    fin_cases j <;> simp [Pi.mul_apply, swp_mul_swi, swi_mul_swp]
  · rw [← map_mul, ← map_mul]
    congr 1
    funext j
    fin_cases j <;> simp [Pi.mul_apply, swp_mul_swp, swi_mul_swi]
  · rw [hyy]
    exact spPlane_neg_one_mem_center 2
  · rw [hyy, ← map_mul]
    convert map_one (spPlane (K := GaloisField 3 1) 2) using 2
    funext j
    simp [Pi.mul_apply]
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    have h1 := hc (spPlane 2 ![sru, 1])
    rw [← map_mul, ← map_mul] at h1
    have h3 := congrFun (spPlane_injective 2 h1) 0
    simp [Pi.mul_apply] at h3
    exact sru_mul_swp_ne h3
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    have h1 := hc (spPlane 2 ![sru, 1])
    rw [← map_mul, ← map_mul] at h1
    have h3 := congrFun (spPlane_injective 2 h1) 0
    simp [Pi.mul_apply] at h3
    exact sru_mul_swp_ne h3
  · intro hc
    rw [Subgroup.mem_center_iff] at hc
    rw [hyy'] at hc
    have h1 := hc planeSwap
    have h2 := congrArg (fun g : StatedSp 2 (GaloisField 3 1) =>
      ((g : GL (Fin 2 ⊕ Fin 2) (GaloisField 3 1)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
        (GaloisField 3 1)) (Sum.inl 0) (Sum.inl 1)) h1
    simp [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      spPlane_val, planeMat, planeSwap, pswap, Matrix.diagonal_apply] at h2
    exact neg_one_ne_one_gf3 h2.symm

end Main

end CFSG.ClassicalInvolution.Q3.Q3YS
