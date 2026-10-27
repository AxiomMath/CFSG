module

public import CFSG.HardMathSupport.U4FF.ClassTmodIrr

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def torusDiag (n : ℕ) (u v : Kˣ) : Fin 4 → Kˣ :=
  ![u, u⁻¹ * v, u ^ 2 ^ n * v⁻¹, (u ^ 2 ^ n)⁻¹]

@[expose] noncomputable def torusGL (n : ℕ) (u v : Kˣ) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mk'' (diagonal fun i => (torusDiag n u v i : K)) (by
    rw [det_diagonal, ← Units.coe_prod]
    exact Units.isUnit _)

theorem torusGL_val (u v : Kˣ) :
    ((torusGL n u v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun i => (torusDiag n u v i : K) := rfl

theorem torusGL_mem (hK : Nat.card K = (2 ^ n) ^ 2) (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v) :
    torusGL n u v ∈ SU (unitaryInvolution K 2 n) 4 := by
  have hu2 : ((u : K) ^ 2 ^ n) ^ 2 ^ n = u := pow_pow_of_card hK u
  refine ⟨?_, ?_⟩
  · rw [torusGL_val, det_diagonal, Fin.prod_univ_four]
    simp only [torusDiag]
    simp
    field_simp
  · rw [torusGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_four, diagonal_apply,
        torusDiag, unitaryInvolution_apply, iterateFrobenius_def, hv, hu2] <;> field_simp
    all_goals first
      | (rw [div_pow, hv]; field_simp; done)
      | (rw [div_pow, hv]; field_simp; exact hu2)
      | (rw [div_pow, hu2, hv]; field_simp; done)

@[expose] noncomputable def torusElt (hK : Nat.card K = (2 ^ n) ^ 2) (u v : Kˣ)
    (hv : (v : K) ^ 2 ^ n = v) : SU4 K n :=
  ⟨torusGL n u v, torusGL_mem hK u v hv⟩

theorem torusElt_val (hK : Nat.card K = (2 ^ n) ^ 2) (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v) :
    (((torusElt hK u v hv : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun i => (torusDiag n u v i : K) := rfl

theorem torusElt_offdiag (hK : Nat.card K = (2 ^ n) ^ 2) (u v : Kˣ) (hv : (v : K) ^ 2 ^ n = v) :
    ∀ i j, i ≠ j →
      (((torusElt hK u v hv : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
  intro i j hij
  rw [torusElt_val]
  exact diagonal_apply_ne _ hij

theorem prod_ite_pow {k : Type*} [Field k] (x : k) (p : Fin n → Bool) (f : Fin n → ℕ) :
    ∏ i : Fin n, (if p i then x ^ f i else 1) = x ^ ∑ i : Fin n, (if p i then f i else 0) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases p i <;> simp

theorem wtLoc_torus {k : Type*} [Field k] (φ : K →+* k) (a b c : Bool) (u v : Kˣ) :
    wtLoc a b c (fun j => φ (torusDiag n u v j : K)) =
      (if a then φ u else 1) * (if b then φ v else 1) * (if c then φ ((u : K) ^ 2 ^ n) else 1) := by
  have h1 : φ (u : K) * φ ((u⁻¹ * v : Kˣ) : K) = φ v := by
    rw [← map_mul]
    congr 1
    simp
  have h2 : φ (u : K) * φ ((u⁻¹ * v : Kˣ) : K) * φ ((u ^ 2 ^ n * v⁻¹ : Kˣ) : K) =
      φ ((u : K) ^ 2 ^ n) := by
    rw [h1, ← map_mul]
    congr 1
    have hv0 : (v : K) ≠ 0 := v.ne_zero
    simp
    field_simp
  have e0 : φ ((torusDiag n u v 0 : Kˣ) : K) = φ u := rfl
  have e01 : φ ((torusDiag n u v 0 : Kˣ) : K) * φ ((torusDiag n u v 1 : Kˣ) : K) = φ v := h1
  have e012 : φ ((torusDiag n u v 0 : Kˣ) : K) * φ ((torusDiag n u v 1 : Kˣ) : K) *
      φ ((torusDiag n u v 2 : Kˣ) : K) = φ ((u : K) ^ 2 ^ n) := h2
  unfold wtLoc
  simp only []
  rw [e012, e01, e0]

end Torus

section Weight


variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k] [CharP k 2]
  [Algebra K k]

theorem Tmod_torus_weight (hK : Nat.card K = (2 ^ n) ^ 2) (l : Lbl n) (u v : Kˣ)
    (hv : (v : K) ^ 2 ^ n = v) :
    Tmod K l k (torusElt hK u v hv) *ᵥ hwv l k =
      algebraMap K k ((u : K) ^ l.e1 * (v : K) ^ l.e2) • hwv l k := by
  have h := TmodΦ_diag l (fun i => frobTw K k i) (torusElt_offdiag hK u v hv)
  rw [Tmod_eq, h]
  congr 1
  have hmat : ∀ j, (((torusElt hK u v hv : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      j j = (torusDiag n u v j : K) := fun j => by
    rw [torusElt_val]
    simp
  simp only [hmat, wtLoc_torus]
  have hA : ∏ i : Fin n, (if l.a i then frobTw K k i (u : K) else 1) =
      algebraMap K k ((u : K) ^ ∑ i : Fin n, (if l.a i then 2 ^ (i : ℕ) else 0)) := by
    have : ∀ i : Fin n, (if l.a i then frobTw K k i (u : K) else 1) =
        algebraMap K k (if l.a i then (u : K) ^ 2 ^ (i : ℕ) else 1) := by
      intro i
      cases l.a i <;> simp [frobTw_apply]
    simp only [this, ← map_prod, prod_ite_pow]
  have hB : ∏ i : Fin n, (if l.b i then frobTw K k i (v : K) else 1) =
      algebraMap K k ((v : K) ^ ∑ i : Fin n, (if l.b i then 2 ^ (i : ℕ) else 0)) := by
    have : ∀ i : Fin n, (if l.b i then frobTw K k i (v : K) else 1) =
        algebraMap K k (if l.b i then (v : K) ^ 2 ^ (i : ℕ) else 1) := by
      intro i
      cases l.b i <;> simp [frobTw_apply]
    simp only [this, ← map_prod, prod_ite_pow]
  have hC : ∏ i : Fin n, (if l.c i then frobTw K k i ((u : K) ^ 2 ^ n) else 1) =
      algebraMap K k ((u : K) ^ ∑ i : Fin n, (if l.c i then 2 ^ (n + (i : ℕ)) else 0)) := by
    have : ∀ i : Fin n, (if l.c i then frobTw K k i ((u : K) ^ 2 ^ n) else 1) =
        algebraMap K k (if l.c i then (u : K) ^ 2 ^ (n + (i : ℕ)) else 1) := by
      intro i
      cases l.c i <;> simp [frobTw_apply, ← pow_mul, ← pow_add]
    simp only [this, ← map_prod, prod_ite_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hA, hB, hC, Lbl.e1, Lbl.e2, pow_add,
    map_mul, map_mul]
  ring

theorem prod_frob_weight (l : Lbl n) (x w : K) :
    ∏ i : Fin n, ((if l.a i then frobTw K k i x else 1) * (if l.b i then frobTw K k i w else 1) *
        (if l.c i then frobTw K k i (x ^ 2 ^ n) else 1)) =
      algebraMap K k (x ^ l.e1 * w ^ l.e2) := by
  have hA : ∏ i : Fin n, (if l.a i then frobTw K k i x else 1) =
      algebraMap K k (x ^ ∑ i : Fin n, (if l.a i then 2 ^ (i : ℕ) else 0)) := by
    have : ∀ i : Fin n, (if l.a i then frobTw K k i x else 1) =
        algebraMap K k (if l.a i then x ^ 2 ^ (i : ℕ) else 1) := by
      intro i
      cases l.a i <;> simp [frobTw_apply]
    simp only [this, ← map_prod, prod_ite_pow]
  have hB : ∏ i : Fin n, (if l.b i then frobTw K k i w else 1) =
      algebraMap K k (w ^ ∑ i : Fin n, (if l.b i then 2 ^ (i : ℕ) else 0)) := by
    have : ∀ i : Fin n, (if l.b i then frobTw K k i w else 1) =
        algebraMap K k (if l.b i then w ^ 2 ^ (i : ℕ) else 1) := by
      intro i
      cases l.b i <;> simp [frobTw_apply]
    simp only [this, ← map_prod, prod_ite_pow]
  have hC : ∏ i : Fin n, (if l.c i then frobTw K k i (x ^ 2 ^ n) else 1) =
      algebraMap K k (x ^ ∑ i : Fin n, (if l.c i then 2 ^ (n + (i : ℕ)) else 0)) := by
    have : ∀ i : Fin n, (if l.c i then frobTw K k i (x ^ 2 ^ n) else 1) =
        algebraMap K k (if l.c i then x ^ 2 ^ (n + (i : ℕ)) else 1) := by
      intro i
      cases l.c i <;> simp [frobTw_apply, ← pow_mul, ← pow_add]
    simp only [this, ← map_prod, prod_ite_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hA, hB, hC, Lbl.e1, Lbl.e2, pow_add,
    map_mul, map_mul]
  ring

theorem wtLoc_of_rel (φ : K →+* k) (a b c : Bool) (e : Fin 4 → K)
    (hrel : e 0 * e 1 * e 2 = e 0 ^ 2 ^ n) :
    wtLoc a b c (fun j => φ (e j)) =
      (if a then φ (e 0) else 1) * (if b then φ (e 0 * e 1) else 1) *
        (if c then φ (e 0 ^ 2 ^ n) else 1) := by
  have e0 : φ (e 0) * φ (e 1) = φ (e 0 * e 1) := (map_mul φ _ _).symm
  have e1 : φ (e 0 * e 1) * φ (e 2) = φ (e 0 ^ 2 ^ n) := by
    rw [← map_mul, hrel]
  unfold wtLoc
  cases a <;> cases b <;> cases c <;>
    simp only [↓reduceIte, Bool.false_eq_true, if_false, e0, e1]

theorem Tmod_diag_weight (l : Lbl n) {h : SU4 K n}
    (hd : ∀ i j, i ≠ j → ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (hrel : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 *
        ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 *
          ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 =
        (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) ^ 2 ^ n) :
    Tmod K l k h *ᵥ hwv l k =
      algebraMap K k ((((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) ^ l.e1 *
        (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 *
          ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1) ^ l.e2) • hwv l k := by
  have h1 := TmodΦ_diag l (fun i => frobTw K k i) hd
  rw [Tmod_eq, h1]
  congr 1
  rw [← prod_frob_weight (k := k) l]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact wtLoc_of_rel (frobTw K k i) _ _ _ (fun j => ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j)
    hrel

end Weight

end CFSG.HardMathSupport.U4FF
