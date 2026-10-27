module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open Matrix CFSG.GH74

variable {F : Type} [Field F]

section Matrices

def mat1 : Matrix (Fin 4) (Fin 4) F := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

def mat2 : Matrix (Fin 4) (Fin 4) F := !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

def mat3 : Matrix (Fin 4) (Fin 4) F := !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def mat4 : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

def mat4' : Matrix (Fin 4) (Fin 4) F := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

def negU : GL (Fin 4) F := Units.mk (-1) (-1) (by simp) (by simp)

def U1 : GL (Fin 4) F :=
  Units.mk mat1 mat1
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat1, Matrix.mul_apply, Fin.sum_univ_four])
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat1, Matrix.mul_apply, Fin.sum_univ_four])

def U2 : GL (Fin 4) F :=
  Units.mk mat2 mat2
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat2, Matrix.mul_apply, Fin.sum_univ_four])
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat2, Matrix.mul_apply, Fin.sum_univ_four])

def U3 : GL (Fin 4) F :=
  Units.mk mat3 mat3
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat3, Matrix.mul_apply, Fin.sum_univ_four])
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat3, Matrix.mul_apply, Fin.sum_univ_four])

def U4 : GL (Fin 4) F :=
  Units.mk mat4 mat4'
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat4, mat4', Matrix.mul_apply, Fin.sum_univ_four])
    (by ext a b; fin_cases a <;> fin_cases b <;> simp [mat4, mat4', Matrix.mul_apply, Fin.sum_univ_four])

def scalarU (c d : F) (h : c * d = 1) : GL (Fin 4) F :=
  Units.mk (c • (1 : Matrix (Fin 4) (Fin 4) F)) (d • (1 : Matrix (Fin 4) (Fin 4) F))
    (by rw [smul_mul_smul, mul_one, h, one_smul])
    (by rw [smul_mul_smul, mul_one, mul_comm d c, h, one_smul])

def gen (i : F) (hi : i * i = -1) : Fin 5 → GL (Fin 4) F :=
  ![U1, U2, U3, U4, scalarU i (-i) (by linear_combination -hi)]

def sig (k j : Fin 5) : Bool :=
  decide ((k = 0 ∧ j = 2) ∨ (k = 2 ∧ j = 0) ∨ (k = 1 ∧ j = 3) ∨ (k = 3 ∧ j = 1))

def zsU (b : Bool) : GL (Fin 4) F := if b then negU else 1

lemma negU_central (g : GL (Fin 4) F) : negU * g = g * negU := by
  apply Units.ext; simp [negU]

lemma zsU_central (b : Bool) (g : GL (Fin 4) F) : zsU b * g = g * zsU b := by
  cases b
  · simp [zsU]
  · simp only [zsU, if_true]; exact negU_central g

lemma negU_mul_negU : negU * negU = (1 : GL (Fin 4) F) := by
  apply Units.ext; simp [negU]

lemma zsU_mul (a b : Bool) : (zsU (F := F) a) * zsU (F := F) b = zsU (F := F) (xor a b) := by
  cases a <;> cases b <;> simp [zsU, negU_mul_negU]

lemma negU_ne_one (h2 : (2 : F) ≠ 0) : negU ≠ (1 : GL (Fin 4) F) := by
  intro h
  have h' : (-1 : F) = 1 := by
    have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 0) h
    simpa [negU] using this
  exact h2 (by linear_combination (-1 : F) * h')

lemma zsU_inj (h2 : (2 : F) ≠ 0) {a b : Bool} (h : (zsU (F := F) a) = zsU (F := F) b) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (exfalso; exact negU_ne_one h2 (by simpa [zsU] using h))
    | (exfalso; exact negU_ne_one h2 (by simpa [zsU] using h.symm))

lemma gr_0_0 (i : F) (hi : i * i = -1) :
    gen i hi 0 * gen i hi 0 = zsU (sig 0 0) * (gen i hi 0 * gen i hi 0) := by
  simp [gen, sig, zsU]

lemma gr_0_1 (i : F) (hi : i * i = -1) :
    gen i hi 0 * gen i hi 1 = zsU (sig 0 1) * (gen i hi 1 * gen i hi 0) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_0_2 (i : F) (hi : i * i = -1) :
    gen i hi 0 * gen i hi 2 = zsU (sig 0 2) * (gen i hi 2 * gen i hi 0) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_0_3 (i : F) (hi : i * i = -1) :
    gen i hi 0 * gen i hi 3 = zsU (sig 0 3) * (gen i hi 3 * gen i hi 0) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_0_4 (i : F) (hi : i * i = -1) :
    gen i hi 0 * gen i hi 4 = zsU (sig 0 4) * (gen i hi 4 * gen i hi 0) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_1_0 (i : F) (hi : i * i = -1) :
    gen i hi 1 * gen i hi 0 = zsU (sig 1 0) * (gen i hi 0 * gen i hi 1) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_1_1 (i : F) (hi : i * i = -1) :
    gen i hi 1 * gen i hi 1 = zsU (sig 1 1) * (gen i hi 1 * gen i hi 1) := by
  simp [gen, sig, zsU]

lemma gr_1_2 (i : F) (hi : i * i = -1) :
    gen i hi 1 * gen i hi 2 = zsU (sig 1 2) * (gen i hi 2 * gen i hi 1) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_1_3 (i : F) (hi : i * i = -1) :
    gen i hi 1 * gen i hi 3 = zsU (sig 1 3) * (gen i hi 3 * gen i hi 1) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_1_4 (i : F) (hi : i * i = -1) :
    gen i hi 1 * gen i hi 4 = zsU (sig 1 4) * (gen i hi 4 * gen i hi 1) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_2_0 (i : F) (hi : i * i = -1) :
    gen i hi 2 * gen i hi 0 = zsU (sig 2 0) * (gen i hi 0 * gen i hi 2) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_2_1 (i : F) (hi : i * i = -1) :
    gen i hi 2 * gen i hi 1 = zsU (sig 2 1) * (gen i hi 1 * gen i hi 2) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_2_2 (i : F) (hi : i * i = -1) :
    gen i hi 2 * gen i hi 2 = zsU (sig 2 2) * (gen i hi 2 * gen i hi 2) := by
  simp [gen, sig, zsU]

lemma gr_2_3 (i : F) (hi : i * i = -1) :
    gen i hi 2 * gen i hi 3 = zsU (sig 2 3) * (gen i hi 3 * gen i hi 2) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_2_4 (i : F) (hi : i * i = -1) :
    gen i hi 2 * gen i hi 4 = zsU (sig 2 4) * (gen i hi 4 * gen i hi 2) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_3_0 (i : F) (hi : i * i = -1) :
    gen i hi 3 * gen i hi 0 = zsU (sig 3 0) * (gen i hi 0 * gen i hi 3) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_3_1 (i : F) (hi : i * i = -1) :
    gen i hi 3 * gen i hi 1 = zsU (sig 3 1) * (gen i hi 1 * gen i hi 3) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_3_2 (i : F) (hi : i * i = -1) :
    gen i hi 3 * gen i hi 2 = zsU (sig 3 2) * (gen i hi 2 * gen i hi 3) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_3_3 (i : F) (hi : i * i = -1) :
    gen i hi 3 * gen i hi 3 = zsU (sig 3 3) * (gen i hi 3 * gen i hi 3) := by
  simp [gen, sig, zsU]

lemma gr_3_4 (i : F) (hi : i * i = -1) :
    gen i hi 3 * gen i hi 4 = zsU (sig 3 4) * (gen i hi 4 * gen i hi 3) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_4_0 (i : F) (hi : i * i = -1) :
    gen i hi 4 * gen i hi 0 = zsU (sig 4 0) * (gen i hi 0 * gen i hi 4) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_4_1 (i : F) (hi : i * i = -1) :
    gen i hi 4 * gen i hi 1 = zsU (sig 4 1) * (gen i hi 1 * gen i hi 4) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_4_2 (i : F) (hi : i * i = -1) :
    gen i hi 4 * gen i hi 2 = zsU (sig 4 2) * (gen i hi 2 * gen i hi 4) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_4_3 (i : F) (hi : i * i = -1) :
    gen i hi 4 * gen i hi 3 = zsU (sig 4 3) * (gen i hi 3 * gen i hi 4) := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, sig, zsU, negU, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4',
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, hi]

lemma gr_4_4 (i : F) (hi : i * i = -1) :
    gen i hi 4 * gen i hi 4 = zsU (sig 4 4) * (gen i hi 4 * gen i hi 4) := by
  simp [gen, sig, zsU]

lemma gen_rel (i : F) (hi : i * i = -1) (k j : Fin 5) :
    gen i hi k * gen i hi j = zsU (sig k j) * (gen i hi j * gen i hi k) := by
  fin_cases k <;> fin_cases j
  · exact gr_0_0 i hi
  · exact gr_0_1 i hi
  · exact gr_0_2 i hi
  · exact gr_0_3 i hi
  · exact gr_0_4 i hi
  · exact gr_1_0 i hi
  · exact gr_1_1 i hi
  · exact gr_1_2 i hi
  · exact gr_1_3 i hi
  · exact gr_1_4 i hi
  · exact gr_2_0 i hi
  · exact gr_2_1 i hi
  · exact gr_2_2 i hi
  · exact gr_2_3 i hi
  · exact gr_2_4 i hi
  · exact gr_3_0 i hi
  · exact gr_3_1 i hi
  · exact gr_3_2 i hi
  · exact gr_3_3 i hi
  · exact gr_3_4 i hi
  · exact gr_4_0 i hi
  · exact gr_4_1 i hi
  · exact gr_4_2 i hi
  · exact gr_4_3 i hi
  · exact gr_4_4 i hi

def fac (i : F) (hi : i * i = -1) (e : Bool) (j : Fin 5) : GL (Fin 4) F :=
  if e then gen i hi j else 1

lemma fac_rel (i : F) (hi : i * i = -1) (k j : Fin 5) (e : Bool) :
    gen i hi k * fac i hi e j = zsU (e && sig k j) * (fac i hi e j * gen i hi k) := by
  cases e
  · simp [fac, zsU]
  · simp only [fac, Bool.true_and, if_true]
    exact gen_rel i hi k j

lemma comm_mul {g x y : GL (Fin 4) F} {a c : Bool} (hx : g * x = zsU a * (x * g))
    (hy : g * y = zsU c * (y * g)) : g * (x * y) = zsU (xor a c) * ((x * y) * g) := by
  have hc : Commute x (zsU (F := F) c) := (zsU_central c x).symm
  calc g * (x * y) = (g * x) * y := (mul_assoc g x y).symm
    _ = zsU a * (x * (g * y)) := by rw [hx]; simp only [mul_assoc]
    _ = zsU a * (x * (zsU c * (y * g))) := by rw [hy]
    _ = zsU a * (zsU c * (x * (y * g))) := by rw [hc.left_comm (y * g)]
    _ = (zsU a * zsU c) * (x * (y * g)) := (mul_assoc _ _ _).symm
    _ = zsU (xor a c) * ((x * y) * g) := by rw [zsU_mul, mul_assoc x y g]

def prodE (i : F) (hi : i * i = -1) (e : Fin 5 → Bool) : GL (Fin 4) F :=
  fac i hi (e 0) 0 * (fac i hi (e 1) 1 * (fac i hi (e 2) 2 * (fac i hi (e 3) 3 * fac i hi (e 4) 4)))

def sgnE (e : Fin 5 → Bool) (k : Fin 5) : Bool :=
  xor (e 0 && sig k 0) (xor (e 1 && sig k 1) (xor (e 2 && sig k 2)
    (xor (e 3 && sig k 3) (e 4 && sig k 4))))

lemma prodE_rel (i : F) (hi : i * i = -1) (e : Fin 5 → Bool) (k : Fin 5) :
    gen i hi k * prodE i hi e = zsU (sgnE e k) * (prodE i hi e * gen i hi k) := by
  have h3 := comm_mul (fac_rel i hi k 3 (e 3)) (fac_rel i hi k 4 (e 4))
  have h2 := comm_mul (fac_rel i hi k 2 (e 2)) h3
  have h1 := comm_mul (fac_rel i hi k 1 (e 1)) h2
  exact comm_mul (fac_rel i hi k 0 (e 0)) h1

lemma sgn_eq_iff (e e' : Fin 5 → Bool) (h : ∀ k, sgnE e k = sgnE e' k) :
    e 0 = e' 0 ∧ e 1 = e' 1 ∧ e 2 = e' 2 ∧ e 3 = e' 3 :=
  ⟨by simpa [sgnE, sig] using h 2, by simpa [sgnE, sig] using h 3,
    by simpa [sgnE, sig] using h 0, by simpa [sgnE, sig] using h 1⟩

def Hgrp (i : F) (hi : i * i = -1) : Subgroup (GL (Fin 4) F) :=
  Subgroup.closure (Set.range (gen i hi))

lemma gen_mem (i : F) (hi : i * i = -1) (k : Fin 5) : gen i hi k ∈ Hgrp i hi :=
  Subgroup.subset_closure ⟨k, rfl⟩

lemma U4_sq : U4 * U4 = (negU : GL (Fin 4) F) := by
  apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
    simp [U4, negU, mat4, mat4', Matrix.mul_apply, Fin.sum_univ_four]

lemma negU_mem (i : F) (hi : i * i = -1) : (negU : GL (Fin 4) F) ∈ Hgrp i hi := by
  rw [← U4_sq]
  exact (Hgrp i hi).mul_mem (gen_mem i hi 3) (gen_mem i hi 3)

lemma zsU_mem (i : F) (hi : i * i = -1) (b : Bool) : zsU (F := F) b ∈ Hgrp i hi := by
  cases b
  · simpa [zsU] using (Hgrp i hi).one_mem
  · simpa [zsU] using negU_mem i hi

lemma fac_mem (i : F) (hi : i * i = -1) (e : Bool) (j : Fin 5) : fac i hi e j ∈ Hgrp i hi := by
  cases e
  · simpa [fac] using (Hgrp i hi).one_mem
  · simpa [fac] using gen_mem i hi j

lemma prodE_mem (i : F) (hi : i * i = -1) (e : Fin 5 → Bool) : prodE i hi e ∈ Hgrp i hi :=
  (Hgrp i hi).mul_mem (fac_mem i hi _ _) ((Hgrp i hi).mul_mem (fac_mem i hi _ _)
    ((Hgrp i hi).mul_mem (fac_mem i hi _ _) ((Hgrp i hi).mul_mem (fac_mem i hi _ _)
      (fac_mem i hi _ _))))

lemma prodE_eq (i : F) (hi : i * i = -1) (e : Fin 5 → Bool) :
    prodE i hi e = (fac i hi (e 0) 0 * (fac i hi (e 1) 1 * (fac i hi (e 2) 2 *
      fac i hi (e 3) 3))) * fac i hi (e 4) 4 := by
  simp only [prodE, mul_assoc]

lemma gsq_0 (i : F) (hi : i * i = -1) : gen i hi 0 * gen i hi 0 = 1 := by
  apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, mat1, Matrix.mul_apply, Fin.sum_univ_four]

lemma gsq_1 (i : F) (hi : i * i = -1) : gen i hi 1 * gen i hi 1 = 1 := by
  apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U2, mat2, Matrix.mul_apply, Fin.sum_univ_four]

lemma gsq_2 (i : F) (hi : i * i = -1) : gen i hi 2 * gen i hi 2 = 1 := by
  apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U3, mat3, Matrix.mul_apply, Fin.sum_univ_four]

lemma gsq_3 (i : F) (hi : i * i = -1) : gen i hi 3 * gen i hi 3 = negU := by
  rw [show gen i hi 3 = U4 from rfl, U4_sq]

lemma gsq_4 (i : F) (hi : i * i = -1) : gen i hi 4 * gen i hi 4 = negU := by
  apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, scalarU, negU, hi, Matrix.one_apply]

lemma gen_sq_mem (i : F) (hi : i * i = -1) (k : Fin 5) :
    gen i hi k * gen i hi k = 1 ∨ gen i hi k * gen i hi k = negU := by
  fin_cases k
  · exact Or.inl (gsq_0 i hi)
  · exact Or.inl (gsq_1 i hi)
  · exact Or.inl (gsq_2 i hi)
  · exact Or.inr (gsq_3 i hi)
  · exact Or.inr (gsq_4 i hi)

lemma gen4_ne_zsU (i : F) (hi : i * i = -1) (h2 : (2 : F) ≠ 0) (b : Bool) :
    gen i hi 4 ≠ zsU (F := F) b := by
  intro h
  have h00 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 0) h
  cases b
  · simp [gen, scalarU, zsU] at h00
    subst h00
    exact h2 (by linear_combination hi)
  · simp [gen, scalarU, zsU, negU] at h00
    subst h00
    exact h2 (by linear_combination hi)

lemma gen4_mul_zsU_ne_one (i : F) (hi : i * i = -1) (h2 : (2 : F) ≠ 0) (b : Bool) :
    gen i hi 4 * zsU (F := F) b ≠ 1 := by
  intro h
  apply gen4_ne_zsU i hi h2 b
  have hbb : zsU (F := F) b * zsU (F := F) b = 1 := by
    rw [zsU_mul, Bool.xor_self]; simp [zsU]
  calc gen i hi 4 = gen i hi 4 * (zsU b * zsU b) := by rw [hbb, mul_one]
    _ = (gen i hi 4 * zsU b) * zsU b := by rw [mul_assoc]
    _ = zsU b := by rw [h, one_mul]

lemma negU_zpow (k : ℤ) : ∃ c : Bool, (negU : GL (Fin 4) F) ^ k = zsU (F := F) c := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · refine ⟨false, ?_⟩
    have h2 : (negU : GL (Fin 4) F) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, negU_mul_negU]
    rw [_root_.zpow_mul, h2, _root_.one_zpow]; simp [zsU]
  · refine ⟨true, ?_⟩
    have h2 : (negU : GL (Fin 4) F) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, negU_mul_negU]
    rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul, _root_.zpow_one]; simp [zsU]

lemma elemAbelian_closure {G : Type*} [Group G] (S : Set G)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hs : ∀ x ∈ S, x ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) := by
  have hS : S ⊆ (Subgroup.centralizer S : Set G) := fun s hs' =>
    Subgroup.mem_centralizer_iff.mpr (fun t ht => hc t ht s hs')
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr hS
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hxx := Subgroup.closure_le_centralizer_centralizer S hx
    exact (Subgroup.mem_centralizer_iff.mp hxx y (hcl hy)).symm
  have hsq : ∀ x ∈ Subgroup.closure S, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hs x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [(show Commute x y from hcomm x hx y hy).mul_pow 2, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hsq x hx⟩

lemma sign_eq_of (h2 : (2 : F) ≠ 0) {b s s' : Bool} {X : GL (Fin 4) F}
    (h : zsU (F := F) b * zsU (F := F) s * X = zsU (F := F) s' * zsU (F := F) b * X) :
    s = s' := by
  rw [zsU_mul, zsU_mul] at h
  have h' := zsU_inj h2 (mul_right_cancel h)
  cases b <;> cases s <;> cases s' <;> simp_all

lemma neg_one_eq_zsU : (-1 : GL (Fin 4) F) = zsU (F := F) true := by
  apply Units.ext; simp [zsU, negU]

lemma exists_zsU_of_inv (x y : GL (Fin 4) F) (c : Bool)
    (h : (x * zsU (F := F) c)⁻¹ * y = 1 ∨ (x * zsU (F := F) c)⁻¹ * y = -1) :
    ∃ d : Bool, y = x * zsU (F := F) d := by
  rcases h with h | h
  · exact ⟨c, (inv_mul_eq_one.mp h).symm⟩
  · refine ⟨xor c true, ?_⟩
    calc y = (x * zsU (F := F) c) * ((x * zsU (F := F) c)⁻¹ * y) :=
          (mul_inv_cancel_left _ _).symm
      _ = (x * zsU (F := F) c) * zsU (F := F) true := by rw [h, neg_one_eq_zsU]
      _ = x * zsU (F := F) (xor c true) := by rw [mul_assoc, zsU_mul]

lemma inj_core (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) (e e' : Fin 5 → Bool) (d : Bool)
    (h : prodE i hi e' = prodE i hi e * zsU (F := F) d) : e = e' := by
  have hP : prodE i hi e' = zsU (F := F) d * prodE i hi e := by
    rw [h, zsU_central]
  have hs : ∀ k, sgnE e k = sgnE e' k := by
    intro k
    have hA := prodE_rel i hi e' k
    have hB := prodE_rel i hi e k
    have key : zsU (F := F) d * (zsU (F := F) (sgnE e k) * (prodE i hi e * gen i hi k)) =
        zsU (F := F) (sgnE e' k) * (zsU (F := F) d * (prodE i hi e * gen i hi k)) := by
      calc zsU (F := F) d * (zsU (F := F) (sgnE e k) * (prodE i hi e * gen i hi k))
          = zsU (F := F) d * (gen i hi k * prodE i hi e) := by rw [hB]
        _ = gen i hi k * (zsU (F := F) d * prodE i hi e) :=
          ((show Commute (gen i hi k) (zsU (F := F) d) from (zsU_central d _).symm).left_comm _).symm
        _ = gen i hi k * prodE i hi e' := by rw [hP]
        _ = zsU (F := F) (sgnE e' k) * (prodE i hi e' * gen i hi k) := hA
        _ = zsU (F := F) (sgnE e' k) * (zsU (F := F) d * (prodE i hi e * gen i hi k)) := by
          rw [hP, mul_assoc]
    exact sign_eq_of h2 (by rw [mul_assoc, mul_assoc]; exact key)
  obtain ⟨h0, h1, h2', h3⟩ := sgn_eq_iff e e' hs
  by_cases h4 : e 4 = e' 4
  · refine funext fun j => ?_
    fin_cases j <;> assumption
  · exfalso
    have hQ : fac i hi (e 0) 0 * (fac i hi (e 1) 1 * (fac i hi (e 2) 2 * fac i hi (e 3) 3)) =
        fac i hi (e' 0) 0 * (fac i hi (e' 1) 1 * (fac i hi (e' 2) 2 * fac i hi (e' 3) 3)) := by
      rw [← h0, ← h1, ← h2', ← h3]
    have hf0 := h
    rw [prodE_eq, prodE_eq, ← hQ] at hf0
    have hf := mul_left_cancel (hf0.trans (mul_assoc _ _ _))
    cases hA : e 4 <;> cases hB : e' 4 <;> simp only [hA, hB] at h4 hf
    · simp at h4
    · exact gen4_ne_zsU i hi h2 d (by simpa [fac] using hf)
    · exact gen4_mul_zsU_ne_one i hi h2 d (by simpa [fac] using hf.symm)
    · simp at h4

theorem core_contra [Finite F] (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    (T : Subgroup (GL (Fin 4) F)) (hT : ∀ k, gen i hi k ∈ T)
    {Y : Type} [Group Y] (φ : T →* Y)
    (hker : ∀ g ∈ φ.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1)
    (hY : CFSG.GH74.Gen4 Y) : False := by
  have hHT : Hgrp i hi ≤ T := by
    unfold Hgrp
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hT k
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Hgrp i hi →* Y, ∀ x : Hgrp i hi, ψ x = φ ⟨x.1, hHT x.2⟩ :=
    ⟨φ.comp (Subgroup.inclusion hHT), fun x => rfl⟩
  haveI hPf : Finite ψ.range :=
    Finite.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  obtain ⟨w, hw⟩ : ∃ w : ψ.range, (w : Y) = ψ ⟨negU, negU_mem i hi⟩ :=
    ⟨⟨ψ ⟨negU, negU_mem i hi⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩, rfl⟩
  have hwc : ∀ p : ψ.range, p * w = w * p := by
    intro p
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp p.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hw, ← hx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (negU_central x.1).symm
  have hN : (Subgroup.zpowers w).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((show Commute g w from hwc g).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
  haveI := hN
  obtain ⟨πQ, hπQ⟩ : ∃ π : Hgrp i hi →* (ψ.range ⧸ Subgroup.zpowers w),
      ∀ x : Hgrp i hi, π x = QuotientGroup.mk ⟨ψ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :=
    ⟨(QuotientGroup.mk' (Subgroup.zpowers w)).comp ψ.rangeRestrict, fun x => rfl⟩
  have hπzs : ∀ b : Bool, πQ ⟨zsU b, zsU_mem i hi b⟩ = 1 := by
    intro b
    rw [hπQ, QuotientGroup.eq_one_iff]
    cases b
    · have h1 : ψ ⟨zsU false, zsU_mem i hi false⟩ = 1 := by
        rw [show (⟨zsU false, zsU_mem i hi false⟩ : Hgrp i hi) = 1 from
          Subtype.ext (by simp [zsU]), map_one]
      have h1' : (⟨ψ ⟨zsU false, zsU_mem i hi false⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ :
          ψ.range) = 1 := Subtype.ext h1
      rw [h1']
      exact (Subgroup.zpowers w).one_mem
    · have hz : (⟨ψ ⟨zsU true, zsU_mem i hi true⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ψ.range) = w :=
        Subtype.ext (by
          rw [hw]
          congr 1)
      rw [hz]
      exact Subgroup.mem_zpowers w
  set S : Set (ψ.range ⧸ Subgroup.zpowers w) :=
    Set.range (fun k : Fin 5 => πQ ⟨gen i hi k, gen_mem i hi k⟩) with hS
  have key : ∀ g (hg : g ∈ Subgroup.closure (Set.range (gen i hi))),
      ∃ hg' : g ∈ Hgrp i hi, πQ ⟨g, hg'⟩ ∈ Subgroup.closure S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨gen_mem i hi k, Subgroup.subset_closure ⟨k, rfl⟩⟩
    | one =>
      refine ⟨(Hgrp i hi).one_mem, ?_⟩
      rw [show (⟨1, (Hgrp i hi).one_mem⟩ : Hgrp i hi) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      obtain ⟨hx', hxS⟩ := ihx
      obtain ⟨hy', hyS⟩ := ihy
      refine ⟨(Hgrp i hi).mul_mem hx' hy', ?_⟩
      rw [show (⟨x * y, (Hgrp i hi).mul_mem hx' hy'⟩ : Hgrp i hi) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl,
        map_mul]
      exact Subgroup.mul_mem _ hxS hyS
    | inv x hx ih =>
      obtain ⟨hx', hxS⟩ := ih
      refine ⟨(Hgrp i hi).inv_mem hx', ?_⟩
      rw [show (⟨x⁻¹, (Hgrp i hi).inv_mem hx'⟩ : Hgrp i hi) = (⟨x, hx'⟩)⁻¹ from rfl, map_inv]
      exact Subgroup.inv_mem _ hxS
  have hall : ∀ x : Hgrp i hi, πQ x ∈ Subgroup.closure S := by
    intro x
    obtain ⟨_, hxS⟩ := key x.1 x.2
    exact hxS
  have hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨k, rfl⟩ _ ⟨j, rfl⟩
    dsimp only
    rw [← map_mul, ← map_mul]
    have h : (⟨gen i hi k, gen_mem i hi k⟩ : Hgrp i hi) * ⟨gen i hi j, gen_mem i hi j⟩ =
        ⟨zsU (sig k j), zsU_mem i hi _⟩ *
          (⟨gen i hi j, gen_mem i hi j⟩ * ⟨gen i hi k, gen_mem i hi k⟩) :=
      Subtype.ext (gen_rel i hi k j)
    rw [h, map_mul, hπzs, one_mul]
  have hs : ∀ x ∈ S, x ^ 2 = 1 := by
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [sq, ← map_mul]
    rcases gen_sq_mem i hi k with h | h
    · rw [show (⟨gen i hi k, gen_mem i hi k⟩ * ⟨gen i hi k, gen_mem i hi k⟩ : Hgrp i hi) = 1 from
        Subtype.ext h, map_one]
    · rw [show (⟨gen i hi k, gen_mem i hi k⟩ * ⟨gen i hi k, gen_mem i hi k⟩ : Hgrp i hi) =
          ⟨zsU true, zsU_mem i hi true⟩ from Subtype.ext (by simp [zsU, h]), hπzs]
  have hE : CFSG.Open.IsElemAbelian 2 (Subgroup.closure S) := elemAbelian_closure S hc hs
  have hG : CFSG.GH74.Gen4 (ψ.range ⧸ Subgroup.zpowers w) :=
    CFSG.GH74.Gen4.quotient (Subgroup.zpowers w) (CFSG.GH74.Gen4.subgroup ψ.range hY)
  have hcard := CFSG.GH74.SectionalTwoRankLE.card_le_of_elementary hG (Subgroup.closure S) hE
  let f : (Fin 5 → Bool) → Subgroup.closure S :=
    fun e => ⟨πQ ⟨prodE i hi e, prodE_mem i hi e⟩, hall _⟩
  have hinj : Function.Injective f := by
    intro e e' hee
    have h1 : πQ ⟨prodE i hi e, prodE_mem i hi e⟩ = πQ ⟨prodE i hi e', prodE_mem i hi e'⟩ :=
      congrArg Subtype.val hee
    rw [hπQ, hπQ, QuotientGroup.eq] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, hw] at hk'
    have hab : ψ ((⟨prodE i hi e, prodE_mem i hi e⟩ : Hgrp i hi) *
        (⟨negU, negU_mem i hi⟩ : Hgrp i hi) ^ k) = ψ ⟨prodE i hi e', prodE_mem i hi e'⟩ := by
      rw [map_mul, map_zpow, hk', mul_inv_cancel_left]
    have hg0 : ψ ((((⟨prodE i hi e, prodE_mem i hi e⟩ : Hgrp i hi) *
        (⟨negU, negU_mem i hi⟩ : Hgrp i hi) ^ k)⁻¹) * ⟨prodE i hi e', prodE_mem i hi e'⟩) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨c, hc'⟩ := negU_zpow (F := F) k
    have hker0 := hker ⟨_, hHT ((((⟨prodE i hi e, prodE_mem i hi e⟩ : Hgrp i hi) *
        (⟨negU, negU_mem i hi⟩ : Hgrp i hi) ^ k)⁻¹) * ⟨prodE i hi e', prodE_mem i hi e'⟩).2⟩
      (MonoidHom.mem_ker.mpr ((hψ _).symm.trans hg0))
    have hk1 : ((prodE i hi e) * zsU (F := F) c)⁻¹ * prodE i hi e' = 1 ∨
        ((prodE i hi e) * zsU (F := F) c)⁻¹ * prodE i hi e' = -1 := by
      simpa [Subgroup.coe_zpow, hc'] using hker0
    obtain ⟨d, hd⟩ := exists_zsU_of_inv _ _ c hk1
    exact inj_core h2 hi e e' d hd
  have hle : Nat.card (Fin 5 → Bool) ≤ Nat.card (Subgroup.closure S) :=
    Nat.card_le_card_of_injective f hinj
  have h32 : Nat.card (Fin 5 → Bool) = 32 := by simp [Nat.card_eq_fintype_card]
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h16] at hcard
  omega

end Matrices

lemma usu_pre (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    i ^ q = -i ∧ (-1 : F) ^ q = -1 := by
  refine ⟨?_, Odd.neg_one_pow hq⟩
  obtain ⟨m, hm⟩ : ∃ m, q = 4 * m + 3 := ⟨q / 4, by omega⟩
  rw [hm, _root_.pow_add, _root_.pow_mul, show i ^ 4 = 1 by linear_combination (i * i - 1) * hi,
    _root_.one_pow, one_mul]
  linear_combination i * hi

lemma det4_expand (M : Matrix (Fin 4) (Fin 4) F) :
    M.det = M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
      M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
      M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
      M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp
  ring

lemma det_0 (i : F) (hi : i * i = -1) :
    ((gen i hi 0 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [det4_expand]
  simp [gen, U1, mat1] <;> ring

lemma unit_0 (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    (((gen i hi 0 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      ((gen i hi 0 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨hiq, hneg⟩ := usu_pre q hq hq4 i hi
  have hq0 : q ≠ 0 := by omega
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4', hiq, hneg, hq0,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, zero_pow hq0, one_pow, hi] <;> ring

lemma det_1 (i : F) (hi : i * i = -1) :
    ((gen i hi 1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h4 : i ^ 4 = 1 := by linear_combination (i * i - 1) * hi
  simp +decide [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.det_smul, h4] <;> ring

lemma unit_1 (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    (((gen i hi 1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      ((gen i hi 1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨hiq, hneg⟩ := usu_pre q hq hq4 i hi
  have hq0 : q ≠ 0 := by omega
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4', hiq, hneg, hq0,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, zero_pow hq0, one_pow, hi] <;> ring

lemma det_2 (i : F) (hi : i * i = -1) :
    ((gen i hi 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h4 : i ^ 4 = 1 := by linear_combination (i * i - 1) * hi
  simp +decide [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.det_smul, h4] <;> ring

lemma unit_2 (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    (((gen i hi 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      ((gen i hi 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨hiq, hneg⟩ := usu_pre q hq hq4 i hi
  have hq0 : q ≠ 0 := by omega
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4', hiq, hneg, hq0,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, zero_pow hq0, one_pow, hi] <;> ring

lemma det_3 (i : F) (hi : i * i = -1) :
    ((gen i hi 3 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [det4_expand]
  simp [gen, U4, mat4] <;> ring

lemma unit_3 (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    (((gen i hi 3 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      ((gen i hi 3 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨hiq, hneg⟩ := usu_pre q hq hq4 i hi
  have hq0 : q ≠ 0 := by omega
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4', hiq, hneg, hq0,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, zero_pow hq0, one_pow, hi] <;> ring

lemma det_4 (i : F) (hi : i * i = -1) :
    ((gen i hi 4 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h4 : i ^ 4 = 1 := by linear_combination (i * i - 1) * hi
  simp +decide [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.det_smul, h4] <;> ring

lemma unit_4 (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) :
    (((gen i hi 4 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      ((gen i hi 4 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨hiq, hneg⟩ := usu_pre q hq hq4 i hi
  have hq0 : q ≠ 0 := by omega
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [gen, U1, U2, U3, U4, scalarU, mat1, mat2, mat3, mat4, mat4', hiq, hneg, hq0,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.map_apply, zero_pow hq0, one_pow, hi] <;> ring

theorem mem_statedSU_of_unitary {q : ℕ} {A : GL (Fin 4) F}
    (h1 : (A : Matrix (Fin 4) (Fin 4) F).det = 1)
    (h2 : ((A : Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ * (A : Matrix (Fin 4) (Fin 4) F) = 1) :
    A ∈ CFSG.Open.StatedSU 4 q F := by
  unfold CFSG.Open.StatedSU
  exact Subgroup.subset_closure ⟨h1, h2⟩

lemma gen_mem_SL (i : F) (hi : i * i = -1) (k : Fin 5) :
    gen i hi k ∈ CFSG.Open.StatedSL 4 F := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  fin_cases k
  · exact det_0 i hi
  · exact det_1 i hi
  · exact det_2 i hi
  · exact det_3 i hi
  · exact det_4 i hi

lemma gen_mem_SU (q : ℕ) (hq : Odd q) (hq4 : q % 4 = 3) (i : F) (hi : i * i = -1) (k : Fin 5) :
    gen i hi k ∈ CFSG.Open.StatedSU 4 q F := by
  fin_cases k
  · exact mem_statedSU_of_unitary (det_0 i hi) (unit_0 q hq hq4 i hi)
  · exact mem_statedSU_of_unitary (det_1 i hi) (unit_1 q hq hq4 i hi)
  · exact mem_statedSU_of_unitary (det_2 i hi) (unit_2 q hq hq4 i hi)
  · exact mem_statedSU_of_unitary (det_3 i hi) (unit_3 q hq hq4 i hi)
  · exact mem_statedSU_of_unitary (det_4 i hi) (unit_4 q hq hq4 i hi)

theorem not_gen4_of_SL4 {F : Type} [Field F] [Finite F] {i : F} (hi : i * i = -1)
    (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (φ : ↥(CFSG.Open.StatedSL 4 F) →* Y)
    (hker : ∀ g ∈ φ.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1) :
    ¬ CFSG.GH74.Gen4 Y :=
  fun hY => core_contra h2 hi (CFSG.Open.StatedSL 4 F) (fun k => gen_mem_SL i hi k) φ hker hY

theorem not_gen4_of_SU4 {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Odd q)
    (hq4 : q % 4 = 3) (hF : Nat.card F = q ^ 2) {i : F} (hi : i * i = -1)
    (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (φ : ↥(CFSG.Open.StatedSU 4 q F) →* Y)
    (hker : ∀ g ∈ φ.ker, (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1) :
    ¬ CFSG.GH74.Gen4 Y :=
  fun hY => core_contra h2 hi (CFSG.Open.StatedSU 4 q F) (fun k => gen_mem_SU q hq hq4 i hi k) φ hker hY

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
