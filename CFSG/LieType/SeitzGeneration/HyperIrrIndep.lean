module

public import CFSG.LieType.SeitzGeneration.HyperIrrData
public import CFSG.LieType.SeitzGeneration.HyperIrrIsolate
public import CFSG.LieType.SeitzGeneration.HyperIrrQuasi

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Module Polynomial

variable {F : Type*} [Field F] {n p : ℕ} {ζ c : F} {A B C : Matrix (Fin n) (Fin n) F}
  {u₀ : Fin n → F}

@[expose] def kvec (A C : Matrix (Fin n) (Fin n) F) (u₀ : Fin n → F) (ij : Fin p × Fin p) :
    Fin n → F :=
  (A ^ (ij.1 : ℕ) * C ^ (ij.2 : ℕ)).mulVec u₀

@[expose] def annIdeal (C : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : Ideal F[X] where
  carrier := {q | (aeval C q).mulVec v = 0}
  add_mem' := fun {a b} (ha : (aeval C a).mulVec v = 0) (hb : (aeval C b).mulVec v = 0) => by
    show (aeval C (a + b)).mulVec v = 0
    rw [map_add, Matrix.add_mulVec, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := fun q a (ha : (aeval C a).mulVec v = 0) => by
    show (aeval C (q • a)).mulVec v = 0
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero]

namespace KronData

theorem zeta_ne_zero (h : KronData p ζ c A B C u₀) : ζ ≠ 0 :=
  h.prim.ne_zero h.prime.ne_zero

theorem B_mul_A_pow (h : KronData p ζ c A B C u₀) (i : ℕ) :
    B * A ^ i = (ζ⁻¹) ^ i • (A ^ i * B) := by
  have hq := pow_mul_quasi h.hAB i
  rw [hq, smul_smul, ← mul_pow, inv_mul_cancel₀ h.zeta_ne_zero, one_pow, one_smul]

theorem kvec_B (h : KronData p ζ c A B C u₀) (ij : Fin p × Fin p) :
    B.mulVec (kvec A C u₀ ij) = (ζ⁻¹ ^ (ij.1 : ℕ)) • kvec A C u₀ ij := by
  have hBC : Commute B (C ^ (ij.2 : ℕ)) := (show Commute B C from h.hBC).pow_right _
  have h1 : B * (A ^ (ij.1 : ℕ) * C ^ (ij.2 : ℕ)) =
      (ζ⁻¹ ^ (ij.1 : ℕ)) • ((A ^ (ij.1 : ℕ) * C ^ (ij.2 : ℕ)) * B) := by
    rw [← Matrix.mul_assoc, h.B_mul_A_pow, Matrix.smul_mul, Matrix.mul_assoc, hBC.eq,
      ← Matrix.mul_assoc]
  rw [kvec, Matrix.mulVec_mulVec, h1, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, h.hBu]

theorem kvec_A (h : KronData p ζ c A B C u₀) (hp : 0 < p) (i j : Fin p) :
    A.mulVec (kvec A C u₀ (i, j)) = kvec A C u₀ (⟨((i : ℕ) + 1) % p, Nat.mod_lt _ hp⟩, j) := by
  simp only [kvec]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ', pow_eq_pow_mod _ h.hA]

theorem kvec_C (h : KronData p ζ c A B C u₀) (hp : 0 < p) (i j : Fin p) :
    C.mulVec (kvec A C u₀ (i, j)) = (if (j : ℕ) + 1 = p then c else 1) •
      kvec A C u₀ (i, ⟨((j : ℕ) + 1) % p, Nat.mod_lt _ hp⟩) := by
  have hAC : Commute C (A ^ (i : ℕ)) := ((show Commute A C from h.hAC).pow_left _).symm
  have hpow : C ^ ((j : ℕ) + 1) =
      (if (j : ℕ) + 1 = p then c else 1) • C ^ (((j : ℕ) + 1) % p) := by
    by_cases hj : (j : ℕ) + 1 = p
    · simp only [hj, ↓reduceIte, Nat.mod_self, pow_zero]
      exact h.hC
    · have hlt : (j : ℕ) + 1 < p := by have := j.2; omega
      simp only [hj, ↓reduceIte, Nat.mod_eq_of_lt hlt, one_smul]
  have key : C * (A ^ (i : ℕ) * C ^ (j : ℕ)) =
      (if (j : ℕ) + 1 = p then c else 1) • (A ^ (i : ℕ) * C ^ (((j : ℕ) + 1) % p)) := by
    rw [← Matrix.mul_assoc, hAC.eq, Matrix.mul_assoc, ← pow_succ', hpow, Matrix.mul_smul]
  simp only [kvec]
  rw [Matrix.mulVec_mulVec, key, Matrix.smul_mulVec]

theorem kvec_zero (hp : 0 < p) : kvec A C u₀ (⟨0, hp⟩, ⟨0, hp⟩) = u₀ := by
  simp [kvec]

theorem span_kvec (h : KronData p ζ c A B C u₀) (hp : 0 < p) :
    ⊤ ≤ Submodule.span F (Set.range (kvec A C u₀ : Fin p × Fin p → Fin n → F)) := by
  set W := Submodule.span F (Set.range (kvec A C u₀ : Fin p × Fin p → Fin n → F)) with hW
  have hstab : ∀ M : Matrix (Fin n) (Fin n) F,
      (∀ ij : Fin p × Fin p, M.mulVec (kvec A C u₀ ij) ∈ W) → ∀ w ∈ W, M.mulVec w ∈ W := by
    intro M hM w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨ij, rfl⟩ := hx; exact hM ij
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W.add_mem hx hy
    | smul r x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem r hx
  have hAW := hstab A (fun ij => by
    obtain ⟨i, j⟩ := ij
    rw [h.kvec_A hp]; exact Submodule.subset_span ⟨_, rfl⟩)
  have hBW := hstab B (fun ij => by
    rw [h.kvec_B]; exact W.smul_mem _ (Submodule.subset_span ⟨ij, rfl⟩))
  have hCW := hstab C (fun ij => by
    obtain ⟨i, j⟩ := ij
    rw [h.kvec_C hp]; exact W.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩))
  rcases h.irr W hAW hBW hCW with h0 | h1
  · exfalso
    have : u₀ ∈ W := by
      rw [← kvec_zero hp (A := A) (C := C) (u₀ := u₀)]
      exact Submodule.subset_span ⟨_, rfl⟩
    rw [h0] at this
    exact h.hu (by simpa using this)
  · exact h1.ge

theorem kvec_Bpow (h : KronData p ζ c A B C u₀) (ij : Fin p × Fin p) (t : ℕ) :
    (B ^ t).mulVec (kvec A C u₀ ij) = ((ζ⁻¹ ^ (ij.1 : ℕ)) ^ t) • kvec A C u₀ ij := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h.kvec_B, smul_smul, pow_succ]

theorem kvec_proj (h : KronData p ζ c A B C u₀) (k : Fin p) (ij : Fin p × Fin p) :
    (∑ t ∈ Finset.range p, ((ζ ^ (k : ℕ)) ^ t) • B ^ t).mulVec (kvec A C u₀ ij) =
      (if k = ij.1 then (p : F) else 0) • kvec A C u₀ ij := by
  have hζ0 := h.zeta_ne_zero
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, h.kvec_Bpow, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hy : ∀ t : ℕ, (ζ ^ (k : ℕ)) ^ t * (ζ⁻¹ ^ (ij.1 : ℕ)) ^ t =
      (ζ ^ (k : ℕ) * ζ⁻¹ ^ (ij.1 : ℕ)) ^ t := fun t => (mul_pow _ _ _).symm
  simp only [hy]
  by_cases hki : k = ij.1
  · simp only [hki, ↓reduceIte]
    have : ζ ^ (ij.1 : ℕ) * ζ⁻¹ ^ (ij.1 : ℕ) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
    rw [this]
    simp
  · simp only [hki, ↓reduceIte]
    have e1 : (ζ ^ (k : ℕ)) ^ p = 1 := by
      rw [← pow_mul, mul_comm (k : ℕ) p, pow_mul, h.prim.pow_eq_one, one_pow]
    have e2 : (ζ⁻¹ ^ (ij.1 : ℕ)) ^ p = 1 := by
      rw [← pow_mul, mul_comm (ij.1 : ℕ) p, pow_mul, inv_pow, h.prim.pow_eq_one, inv_one,
        one_pow]
    have hpow : (ζ ^ (k : ℕ) * ζ⁻¹ ^ (ij.1 : ℕ)) ^ p = 1 := by
      rw [mul_pow, e1, e2, one_mul]
    have hne : ζ ^ (k : ℕ) * ζ⁻¹ ^ (ij.1 : ℕ) ≠ 1 := by
      intro h1
      apply hki
      have h2 : ζ ^ (k : ℕ) = ζ ^ (ij.1 : ℕ) := by
        rw [inv_pow] at h1
        exact (mul_inv_eq_one₀ (pow_ne_zero _ hζ0)).1 h1
      exact Fin.ext (h.prim.pow_inj k.2 ij.1.2 h2)
    exact geom_sum_root_eq_zero hpow hne

theorem poly_eq_zero (h : KronData p ζ c A B C u₀) {q : F[X]}
    (hq : (aeval C q).mulVec u₀ = 0) (hdeg : q.degree < p) : q = 0 := by
  have hf : (X ^ p - Polynomial.C c : F[X]) ∈ annIdeal C u₀ := by
    show (aeval C (X ^ p - Polynomial.C c)).mulVec u₀ = 0
    simp [map_sub, map_pow, aeval_X, aeval_C, h.hC, Algebra.algebraMap_eq_smul_one]
  have hne : annIdeal C u₀ ≠ ⊤ := by
    intro htop
    have h1 : (1 : F[X]) ∈ annIdeal C u₀ := htop ▸ Submodule.mem_top
    have h2 : (aeval C (1 : F[X])).mulVec u₀ = 0 := h1
    rw [map_one, Matrix.one_mulVec] at h2
    exact h.hu h2
  have hmax : (Ideal.span {(X ^ p - Polynomial.C c : F[X])}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (X_pow_sub_C_irreducible_of_prime h.prime h.notPow)
  have hle : Ideal.span {(X ^ p - Polynomial.C c : F[X])} ≤ annIdeal C u₀ :=
    (Ideal.span_singleton_le_iff_mem _).2 hf
  have heq := hmax.eq_of_le hne hle
  have hq1 : q ∈ annIdeal C u₀ := hq
  rw [← heq] at hq1
  refine eq_zero_of_dvd_of_degree_lt (Ideal.mem_span_singleton.1 hq1) ?_
  rw [degree_X_pow_sub_C h.prime.pos]
  exact hdeg

theorem linearIndependent_kvec (h : KronData p ζ c A B C u₀) :
    LinearIndependent F (kvec A C u₀ : Fin p × Fin p → Fin n → F) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpF := h.hpF
  have hslice : ∀ k : Fin p, ∑ j : Fin p, g (k, j) • kvec A C u₀ (k, j) = 0 := by
    intro k
    have h1 := congrArg (Matrix.mulVec (∑ t ∈ Finset.range p, ((ζ ^ (k : ℕ)) ^ t) • B ^ t)) hg
    rw [Matrix.mulVec_zero, Matrix.mulVec_sum, Fintype.sum_prod_type] at h1
    simp only [Matrix.mulVec_smul, h.kvec_proj] at h1
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [Ne.symm hik])
      (fun hk => absurd (Finset.mem_univ k) hk)] at h1
    simp only [↓reduceIte] at h1
    have h2 : (p : F) • ∑ j : Fin p, g (k, j) • kvec A C u₀ (k, j) = 0 := by
      rw [← h1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul, mul_comm]
    exact (smul_eq_zero.1 h2).resolve_left hpF
  intro ⟨k, l⟩
  have hq0 : ∀ q : F[X], q = ∑ j : Fin p, Polynomial.C (g (k, j)) * X ^ (j : ℕ) →
      (aeval C q).mulVec u₀ = 0 := by
    intro q hq
    have hAq : aeval C q = ∑ j : Fin p, g (k, j) • C ^ (j : ℕ) := by
      rw [hq]
      simp [map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]
    have e : (A ^ (k : ℕ) * ∑ j : Fin p, g (k, j) • C ^ (j : ℕ)).mulVec u₀ =
        ∑ j : Fin p, g (k, j) • kvec A C u₀ (k, j) := by
      rw [Matrix.mul_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [kvec, Matrix.mul_smul, Matrix.smul_mulVec]
    rw [hslice k, ← hAq] at e
    have e2 := congrArg (fun v => (A ^ (p - (k : ℕ))).mulVec v) e
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at e2
    rw [← Matrix.mul_assoc, ← pow_add, Nat.sub_add_cancel k.2.le, h.hA, Matrix.one_mul] at e2
    exact e2
  set q : F[X] := ∑ j : Fin p, Polynomial.C (g (k, j)) * X ^ (j : ℕ) with hq
  have hdeg : q.degree < p := degree_sum_fin_lt (fun j => g (k, j))
  have hz := h.poly_eq_zero (hq0 q hq) hdeg
  have hcoeff : q.coeff (l : ℕ) = g (k, l) := by
    rw [hq, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single l]
    · simp
    · intro j _ hj
      have hlj : ¬ (l : ℕ) = (j : ℕ) := fun hlj => hj (Fin.ext hlj.symm)
      simp [hlj]
    · simp
  rw [← hcoeff, hz]
  simp

theorem card_eq_sq (h : KronData p ζ c A B C u₀) : n = p * p := by
  have hp := h.prime.pos
  let b := Basis.mk h.linearIndependent_kvec (h.span_kvec hp)
  have := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin] at this
  exact this

end KronData

end CFSG.LieType.SeitzGeneration
